-- Prove2me | Theorems.Thm_McFadden1974_MLE_concaveOn_L_and_critical_point_max
-- name    : McFadden1974.MLE.concaveOn_L_and_critical_point_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:04:19.01688+00:00
-- url     : https://prove2.me/theorems/f4f4a9c7-580e-4717-9235-9a3b1dc2b872
-- title:
--   Text after (20) — the log-likelihood is concave and maximized at any critical point
-- statement:
--   The conditional logit log-likelihood $L$ of Equation (18) is concave on $\mathbb{R}^K$. Moreover, $L$ is maximized at any critical point: if $\partial L/\partial\theta(\theta) = 0$, then
--   $$L(\theta') \le L(\theta) \quad \text{for all } \theta' \in \mathbb{R}^K.$$
--
--   Concavity turns maximum likelihood estimation into a concave maximization problem, so the first-order condition (19) $= 0$ characterizes the estimator.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 115 (PDF p. 11), unnumbered sentence after Equation (20)

import Mathlib
import Definitions.Def_McFadden1974_MLE_Model

namespace McFadden1974.MLE

open scoped RealInnerProductSpace

/-- **Concavity of the log-likelihood** (unnumbered, text after Equation (20); McFadden, *Conditional Logit Analysis of Qualitative Choice Behavior*, in P. Zarembka (ed.),
*Frontiers in Econometrics*, Academic Press (1974),
p. 115, PDF p. 11): "Since Equation (20) is the negative of a weighted moment matrix of the
independent variables, it is negative semidefinite and the log-likelihood function is concave in
θ. Then L is maximized at any critical point θ where ∂L/∂θ = 0."

Both claims: `L` is concave on `ℝ^K`, and every critical point of `L` is a global maximizer. -/
theorem concaveOn_L_and_critical_point_max
    {K : ℕ} (d : Data K) :
    ConcaveOn ℝ Set.univ d.L ∧
      ∀ θ : EuclideanSpace ℝ (Fin K), HasGradientAt d.L 0 θ →
        ∀ θ' : EuclideanSpace ℝ (Fin K), d.L θ' ≤ d.L θ := by sorry

end McFadden1974.MLE
