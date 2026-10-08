-- Prove2me | Theorems.Thm_McFadden1974_MLE_exists_maximizer_of_axiom6
-- name    : McFadden1974.MLE.exists_maximizer_of_axiom6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:28:32.941934+00:00
-- url     : https://prove2.me/theorems/aa2caaeb-3341-4e61-a222-f886fe05a99e
-- title:
--   Lemma 3, proof — Axiom 6 is sufficient for a maximizer of the log-likelihood
-- statement:
--   In the conditional logit model under Axiom 5, if Axiom 6 holds then the log-likelihood $L$ of Equation (18) attains its maximum: there is $\hat\theta \in \mathbb{R}^K$ with
--   $$L(\theta) \le L(\hat\theta) \quad \text{for all } \theta \in \mathbb{R}^K.$$
--
--   This is the sufficiency half of Lemma 3: the maximum is attained on the compact ball $D = \{\theta : |\theta| \le [-L(0) + C]/b^*\}$.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 117 (PDF p. 13), Lemma 3, proof (sufficiency)

import Mathlib
import Definitions.Def_McFadden1974_MLE_Model
import Definitions.Def_McFadden1974_MLE_Axioms

namespace McFadden1974.MLE

open scoped RealInnerProductSpace

/-- **Lemma 3, proof — sufficiency of Axiom 6** (McFadden, *Conditional Logit Analysis of Qualitative Choice Behavior*, in P. Zarembka (ed.),
*Frontiers in Econometrics*, Academic Press (1974), p. 117, PDF p. 13): "For θ ∉ D,
L(θ) − C ≤ −b*|θ| < L(0) − C. Hence, L can be maximized on the compact set D, and an optimal θ
exists", where `D = {θ | |θ| ≤ [−L(0) + C]/b*}`.

Under the standing Axiom 5, if Axiom 6 holds, the log-likelihood `L` attains a global
maximum on `ℝ^K`. -/
theorem exists_maximizer_of_axiom6
    {K : ℕ} (d : Data K) (h5 : d.Axiom5) (h6 : d.Axiom6) :
    ∃ θhat : EuclideanSpace ℝ (Fin K), ∀ θ, d.L θ ≤ d.L θhat := by sorry

end McFadden1974.MLE
