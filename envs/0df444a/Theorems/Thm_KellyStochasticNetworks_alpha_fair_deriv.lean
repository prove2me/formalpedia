-- Prove2me | Theorems.Thm_KellyStochasticNetworks_alpha_fair_deriv
-- name    : KellyStochasticNetworks.alpha_fair_deriv
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:48:25.184802+00:00
-- url     : https://prove2.me/theorems/6ef8932f-9d01-4234-a59d-ded9a93c3883
-- title:
--   Exercise 8.3 — the derivative is $w_r n_r^\alpha X_r^{-\alpha}$ for every $\alpha$
-- statement:
--   The weighted $\alpha$-fair objective is defined by two formulas, one for $\alpha \ne 1$ and one
--   for $\alpha = 1$:
--   $$G(X) = \sum_r w_r n_r^{\alpha}\frac{X_r^{1-\alpha}}{1-\alpha}, \qquad\qquad
--     G(X) = \sum_r w_r n_r \log X_r .$$
--   Exercise 8.3 observes that this is a single family, because the derivative has the same form in
--   both cases. For $\alpha \in (0,\infty)$, positive weights, positive flow counts and a positive
--   rate vector,
--   $$\frac{\partial G}{\partial X_r}(X) = w_r\,n_r^{\alpha}\,X_r^{-\alpha}.$$
--
--   This is why $\alpha = 1$ is the natural continuation of the family rather than a separate case
--   stapled on: the singularity in $X_r^{1-\alpha}/(1-\alpha)$ at $\alpha = 1$ is removable once a
--   constant is absorbed, and the derivative never notices it. It is also the formula the stability
--   argument uses, through the tangent-plane inequality, where the same expression appears for every
--   $\alpha$ at once.
--
--   **Formalization Note** The partial derivative is stated as an ordinary derivative in the $r$-th
--   coordinate with the others held fixed, so no partial-derivative API is presupposed. The claim
--   covers the defined-by-cases objective, so proving it means handling both branches and checking
--   they agree.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 189 (PDF p. 197), Exercise 8.3: 'Check that the objective function of the problem (8.1) is concave for each of the three cases 0 < alpha < 1, alpha = 1 and 1 < alpha < infinity. Show that the derivative of the objective function with respect to x_r has the same form, namely w_r n_r x_r^{-alpha}, for all alpha in (0, infinity).' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

theorem alpha_fair_deriv {R : ℕ} (w n : Fin R → ℝ) (α : ℝ) (hα : 0 < α)
    (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r) (X : Fin R → ℝ) (hX : ∀ r, 0 < X r) (r : Fin R) :
    HasDerivAt (fun t : ℝ => alphaFairObjective w n α (Function.update X r t))
      (w r * n r ^ α * X r ^ (-α)) (X r) := by sorry

end KellyStochasticNetworks
