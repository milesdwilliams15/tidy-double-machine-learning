#####################################################
# Source code for tidy covariate adjustment helpers #
#####################################################


# packages ----------------------------------------------------------------

# make sure you have the necessary packages
your_packages   <- available.packages()[, 1]
needed_packages <- c("tidyverse",
                     "tidymodels",
                     "lmtest",
                     "sandwich",
                     "lme4",
                     "dotwhisker")
any_missing <- !all(needed_packages %in% your_packages)
if(any_missing) {
  `%nin%` <- Negate(`%in%`)
  which_is_missing <- which(
    needed_packages %nin% your_packages
  )
  stop("You need to install the following packages:\n",
       paste0(needed_packages[which_is_missing], collapse = ", "))
}

# if you have them, load them
library(tidyverse)
library(tidymodels)
library(lmtest)
library(sandwich)
library(lme4)
library(dotwhisker)


# helper "verbs" ----------------------------------------------------------

# these verbs are meant to build on each other so you can
# work step by step in specifying and estimating an observational
# causal effect model.

# causal_spec:
# adds a causal model specification to some data
causal_spec <- function(x = NULL, formula) {
  is_x_adj_obj <- any(class(x) == "adj_obj")
  if(is_x_adj_obj) {
    adj_obj <- x
    attr(adj_obj, "causal_spec") <- formula
  } else {
    adj_obj <- "A tidy covariate adjustment object" 
    attr(adj_obj, "causal_spec") <- formula
    attr(adj_obj, "data") <- x # add data attribute
    class(adj_obj) <- "adj_obj"
  }
  adj_obj # return
}

# adjust_spec: 
# adds an adjustment model specification to some data
adjust_spec <- function(x = NULL, formula) {
  is_x_adj_obj <- any(class(x) == "adj_obj")
  if(is_x_adj_obj) {
    adj_obj <- x
    attr(adj_obj, "adjust_spec") <- formula
  } else {
    adj_obj <- "A tidy covariate adjustment object" 
    attr(adj_obj, "adjust_spec") <- formula
    attr(adj_obj, "data") <- x # add data attribute
    class(adj_obj) <- "adj_obj"
  }
  adj_obj # return
}

# cov_adjust:
# encodes and runs desired covariate adjustment given an 
# adjustment model specification, desired model type, and
# desired model engine. It can also force fixed and random
# effects. It further supports a customized super learner
# adjustment model if given a list of model types. The meta
# super learner model is fit using a regularized regression
# (lasso, ridge, or elastic net) of the response on the 
# model predictions from the list of models given to the 
# function. The penalty and mixture of the regularized regression
# are set to 0.5 and 0.5 respectively (e.g., the default is
# an elastic net with penalty of 0.5).
cov_adjust <- function(x = NULL,
                       model_type = linear_reg("regression"),
                       fixed_and_rand_effs = NULL,
                       clusters = NULL,
                       causal_spec = NULL, 
                       adjust_spec = NULL, 
                       sl_penalty = 0,
                       sl_mixture = 0.5) 
{
  is_x_adj_obj <- any(class(x) == "adj_obj")
  if(is_x_adj_obj) {
    data <- attributes(x)$data
    causal_spec <- attributes(x)$causal_spec
    adjust_spec <- attributes(x)$adjust_spec
    adj_obj <- x
    attr(adj_obj, "fixed_and_rand_effs") <- fixed_and_rand_effs
    attr(adj_obj, "clusters") <- clusters
    attr(adj_obj, "model_type") <- ifelse(
      is.list(model_type),
      "super learner",
      model_type
    )
  } else {
    data <- x
    adj_obj <- "A tidy covariate adjustment object" 
    attr(adj_obj, "causal_spec") <- causal_spec
    attr(adj_obj, "adjust_spec") <- adjust_spec
    attr(adj_obj, "data") <- data # add data attribute
    class(adj_obj) <- "adj_obj"
    attr(adj_obj, "fixed_and_rand_effs") <- fixed_and_rand_effs
    attr(adj_obj, "clusters") <- clusters
    attr(adj_obj, "model_type") <- ifelse(
      is.list(model_type),
      "super learner",
      model_type
    )
  }
  if (causal_spec[[2]] == adjust_spec[[2]]) 
    stop("Covariates formula should be specified without left-hand side variable.")
  lhs <- deparse(causal_spec[[2]])
  rhs1 <- strsplit(deparse(causal_spec[[3]]), " \\+ ")[[1]]
  rhs2 <- unlist(strsplit(deparse(adjust_spec[[2]]), " \\+ "))
  if (!is.null(fixed_and_rand_effs)) {
    fes <- unlist(strsplit(deparse(fixed_and_rand_effs[[2]]), " \\+ "))
    any_res <- str_detect(fes, "\\|")
    rhs <- c(rhs1, rhs2, fes)
  } else {
    rhs <- c(rhs1, rhs2)
    any_res <- FALSE
  }
  if (!is.null(clusters)) 
    rhs <- c(rhs, clusters)
  fullform <- reformulate(rhs, lhs)
  if (any_res) {
    data <- model.frame(lmer(fullform, data = data))
  } else {
    data <- model.frame(fullform, data)
  }
  covmat <- model.matrix(adjust_spec, data = data)[, -1]
  varmat <- cbind(model.frame(causal_spec, data = data)[, 1], 
                  model.matrix(causal_spec, data = data)[, -1])
  if (!is.null(fixed_and_rand_effs)) {
    if (any_res) {
      for (i in 1:ncol(covmat)) {
        covmat[, i] <- resid(lmer(update(fixed_and_rand_effs, 
                                         ci ~ .), data = data %>% mutate(ci = c(covmat[, 
                                                                                       i]))))
      }
      for (i in 1:ncol(varmat)) {
        varmat[, i] <- resid(lmer(update(fixed_and_rand_effs, 
                                         vi ~ .), data = data %>% mutate(vi = c(varmat[, 
                                                                                       i]))))
      }
    }
    else {
      for (i in 1:ncol(covmat)) {
        covmat[, i] <- resid(lm(update(fixed_and_rand_effs, ci ~ 
                                         .), data = data %>% mutate(ci = c(covmat[, 
                                                                                  i]))))
      }
      for (i in 1:ncol(varmat)) {
        varmat[, i] <- resid(lm(update(fixed_and_rand_effs, vi ~ 
                                         .), data = data %>% mutate(vi = c(varmat[, 
                                                                                  i]))))
      }
    }
  }
  if(any(class(model_type)%in%"list")) {
    ymat <- model_type |>
      map_dfc(
        ~ {
          out <- .x |>
            fit_xy(y = varmat[, 1], x = cbind(covmat)) |>
            predict(new_data = cbind(covmat)) 
          colnames(out) <- paste0(class(.x)[1], ".pred")
          out
        }
      ) |>
      mutate(
        yobs = c(varmat[, 1])
      )
    yhat <- linear_reg(penalty = sl_penalty, mixture = sl_mixture) |>
      set_mode("regression") |>
      set_engine("glmnet") |>
      fit(yobs ~ ., data = ymat) |> 
      predict(new_data = ymat) |>
      pull(.pred)
    yres <- varmat[, 1] - yhat
    dmat <- model_type |>
      map_dfc(
        ~ {
          out <- .x |>
            fit_xy(y = varmat[, 2], x = cbind(covmat)) |>
            predict(new_data = cbind(covmat)) 
          colnames(out) <- paste0(class(.x)[1], ".pred")
          out
        }
      ) |>
      mutate(
        dobs = c(varmat[, 2])
      )
    dhat <- linear_reg(penalty = sl_penalty, mixture = sl_mixture) |>
      set_mode("regression") |>
      set_engine("glmnet") |>
      fit(dobs ~ ., data = dmat) |> 
      predict(new_data = dmat) |>
      pull(.pred)
    dres <- varmat[, 2] - dhat
    data <- data |> mutate(yres = yres, dres = dres)
  } else {
    yhat <- model_type |>
      fit_xy(y = varmat[, 1], x = cbind(covmat)) |>
      predict(new_data = cbind(covmat)) |>
      pull(.pred)
    yres <- varmat[, 1] - yhat
    dhat <- model_type |>
      fit_xy(y = varmat[, 2], x = cbind(covmat)) |>
      predict(new_data = cbind(covmat)) |>
      pull(.pred)
    dres <- varmat[, 2] - dhat
    data <- data |> mutate(yres = yres, dres = dres)
  }
  pros_dt <- tibble(
    response = yres,
    explanatory = dres
  )
  if(!is.null(clusters)) pros_dt$clusters <- c(data[, clusters])
  colnames(pros_dt) <- c(lhs, rhs1, paste0("clusters.", clusters))
  pros_dt |>
    specify(causal_spec) -> spec
  if(!is.null(clusters)) spec$clusters <- c(data[, clusters])
  attr(adj_obj, "spec") <- spec
  adj_obj
}

# estimate_cause:
# with covariate adjustment done, now it's time to compute the
# causal estimate of interest.
estimate_cause <- function(
    x,
    spec = NULL
) {
  ## clusters?
  if(any(attributes(attributes(x)$spec)$names == "clusters")) {
    clust <- attributes(x)$spec$clusters
  } else {
    clust <- NULL
  }
  lm(
    attributes(attributes(x)$spec)$formula,
    data = attributes(x)$spec
  ) -> fit
  attr(fit, "clusters") <- clust
  fit
}

# draw_inference:
# next, perform robust inference (clustered if specified in cov_adjust()).
draw_inference <- function(
    x
) {
  x %>%
    coeftest(
      vcov. = vcovCL(., cluster = attributes(x)$clusters, type = "HC1")
    ) |>
    tidy(conf.int = T) 
}

# show_results:
# visualize the results
show_results <- function(
    x, color = "steelblue", 
    vert_line = T,
    style = c("distribution", "dotwhisker")
) {
  if(style[1] == "distribution") {
    vert_lines <- c(0, x$estimate[2])
    lt <- c(2, 1)
    lw <- c(2, 1)
  } else {
    lt <- 2
    lw <- 2
  }
  dwplot(x, style = style[1]) +
    scale_fill_manual(
      values = color
    ) +
    scale_color_manual(
      values = color
    ) +
    labs(
      x = paste0(
        "Point Estimate\n",
        ifelse(style == "distribution",
               "(with Theoretical Distribution)",
               "(with 95% CI)")
      ),
      y = NULL,
      title = "Covariate Adjusted Effect of the\nExplanatory Variable on the Response"
    ) +
    scale_y_discrete(
      breaks = NULL
    ) -> p
  if(vert_line) {
    p + 
      geom_vline(
        xintercept = vert_lines,
        linetype = lt,
        linewidth = lw
      ) 
  } else {
    p
  }
}


# extra validation tools --------------------------------------------------

# cv_adjust: 
# does cross-validation for a selection of adjustment models
cv_adjust <- function(
    model, ...,
    response_model,
    treatment_model,
    data,
    k = 10
) {
  wrk_flws <- workflow_set(
    preproc = list(
      "response" = response_model,
      #response_model,
      "treatment" = treatment_model
      #treatment_model
    ),
    models = list(model, ...)
  ) 
  cat("Workflow is prepped...\n")
  ## k-fold cross-validation data
  cv_dt <- vfold_cv(data, v = k)
  
  cat("Starting cross-validation...\n")
  ## implement in the workflow
  wrk_flws <- wrk_flws |>
    workflow_map(fn = "fit_resamples", 
                 resamples = cv_dt)
  
  cat("DONE!")
  ## collect the results 
  wrk_flws |>
    collect_metrics() |>
    filter(.metric == "rmse") 
}

# cv_show:
# shows results from the cross-validation
cv_show <- function(x) {
  ggplot(x) +
    aes(x = mean, y = model,
        xmin = mean - 1.96 * std_err,
        xmax = mean + 1.96 * std_err) +
    geom_pointrange(
      aes(color = str_extract(wflow_id, "response|treatment")),
      position = ggstance::position_dodgev(-0.2)
    ) +
    labs(
      x = "RMSE",
      y = NULL,
      color = NULL,
      title = "Adjustment Model Comparisons"
    ) 
}

# eff_sample_wts:
eff_sample_wts <- function(x) {
  attributes(x)$spec |>
    pull(2) -> treat_resid
  treat_resid^2
}


# spit out what's available -----------------------------------------------

cat(
  "====================================\n",
  "Available functions:\n\n",
  "- causal_spec(x = NULL, formula)\n",
  "- adjust_spec(x = NULL, formula)\n",
  "- adjust_model(x = NULL,
                  model_type = linear_reg('regression'),
                  fixed_and_rand_effs = NULL,
                  clusters = NULL,
                  causal_spec = NULL, 
                  adjust_spec = NULL, 
                  sl_penalty = 0,
                  sl_mixture = 0.5)\n",
  "- estimate_cause(x, spec = NULL)\n",
  "- draw_inference(x)\n",
  "- show_results(x, color = 'steelblue', 
                  vert_line = T,
                  style = c('distribution', 'dotwhisker'))\n",
  "\nSome additional validation tools:\n\n",
  "- cv_adjust(model, ...,
               response_model,
               treatment_model,
               data,
               k = 10)\n",
  "- cv_show(x)\n",
  "- eff_sample_wts(x)",
  "\n===================================="
)

# examples ----------------------------------------------------------------
if(exists("run_examples")) {
  run_examples <- F
  cat(
    "\n",
    "Note: run_examples == FALSE\n",
    "If you want to run example code, set run_examples <- TRUE then re-run source code."
  )
}

if(run_examples) {
  ## simulate some data
  set.seed(1)
  dt <- tibble(
    id = 1:1000
  ) |>
    mutate(
      # covariates
      x = rnorm(n()),
      z = rnorm(n()),
      
      # the causal variable
      d = x * z + rnorm(n()),
      
      # the response
      # (with treat eff heterogeneity)
      # (true avg effect is ~ 1)
      y = z^2 * d + x^2 * z - z + rnorm(n())
    )
  
  
  ## example workflow with single adjustment model
  dt |>
    # causal model specification
    causal_spec(y ~ d) |>
    # adjustment model specification
    adjust_spec(~ x + z) |>
    # do covariate adjustment with preferred model and engine
    cov_adjust(rand_forest("regression")) |>
    # estimate causal effect of interest
    estimate_cause() |>
    # draw inference
    draw_inference() |>
    # show the results
    show_results()
  
  ## example with super learner adjustment model
  dt |>
    # causal model specification
    causal_spec(y ~ d) |>
    # adjustment model specification
    adjust_spec(~ x + z) |>
    # do covariate adjustment with preferred model and engine
    cov_adjust(
      # list of models
      list(
        linear_reg(),
        rand_forest("regression"),
        parsnip::bart("regression")
      ),
      # regularized regression options
      # to fit super learner
      sl_penalty = 0.5,
      sl_mixture = 0.5
    ) |>
    # estimate causal effect of interest
    estimate_cause() |>
    # draw inference
    draw_inference() |>
    # show the results
    show_results()
}
