-- Prove2me | Theorems.Thm_McFadden1974_MLE_L_sub_C_le_neg_mul_norm
-- name    : McFadden1974.MLE.L_sub_C_le_neg_mul_norm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:28:34.029065+00:00
-- url     : https://prove2.me/theorems/b41c451e-5cbe-4f86-966a-bca134544155
-- title:
--   Lemma 3, proof — the coercivity bound L(θ) − C ≤ −b*|θ|
-- statement:
--   In the conditional logit model, suppose Axioms 5 and 6 hold and $b^* > 0$ satisfies $b^* \le b(\gamma)$ for every unit vector $\gamma$, where $b$ is the function of Equation (21). Then for every $\theta \in \mathbb{R}^K$,
--   $$L(\theta) - C \le -b^*\,|\theta|,$$
--   where $L$ is the log-likelihood (18), $C$ its constant, and $|\theta| = (\theta'\theta)^{1/2}$.
--
--   The bound shows that $L$ tends to $-\infty$ linearly in every direction, so its maximization can be restricted to a compact ball.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), pp. 116-117 (PDF pp. 12-13), Lemma 3, proof

import Mathlib
import Definitions.Def_McFadden1974_MLE_Model
import Definitions.Def_McFadden1974_MLE_Axioms

namespace McFadden1974.MLE

open scoped RealInnerProductSpace

/-- **Lemma 3, proof — the coercivity bound** (McFadden, *Conditional Logit Analysis of Qualitative Choice Behavior*, in P. Zarembka (ed.),
*Frontiers in Econometrics*, Academic Press (1974), pp. 116–117, PDF pp. 12–13):
"Consider any θ ≠ 0, and let γ = θ/|θ|. … From Equation (18),
L(θ) − C ≤ S_in log P_in = … ≤ −b(γ)|θ| ≤ −b*|θ|."

Under the standing Axiom 5 and Axiom 6, if `b* > 0` is a lower bound of `b` (21) on the unit sphere, then
`L(θ) − C ≤ −b*‖θ‖` for every `θ ∈ ℝ^K` (for `θ = 0` both sides are `≤ 0` and `= 0`).

**Formalization Note.** `‖θ‖` is the Euclidean norm `(θ'θ)^{1/2}`. Axiom 5 is inherited from
Lemma 3; Axiom 6 and `0 < b*` are the context of this proof step (b* is the bound of the previous
step). -/
theorem L_sub_C_le_neg_mul_norm
    {K : ℕ} (d : Data K) (h5 : d.Axiom5) (h6 : d.Axiom6) (bstar : ℝ) (hbpos : 0 < bstar)
    (hb : ∀ γ : EuclideanSpace ℝ (Fin K), ‖γ‖ = 1 → bstar ≤ d.b γ)
    (θ : EuclideanSpace ℝ (Fin K)) :
    d.L θ - d.C ≤ -bstar * ‖θ‖ := by sorry

end McFadden1974.MLE
