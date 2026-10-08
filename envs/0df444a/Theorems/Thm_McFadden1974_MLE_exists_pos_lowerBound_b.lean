-- Prove2me | Theorems.Thm_McFadden1974_MLE_exists_pos_lowerBound_b
-- name    : McFadden1974.MLE.exists_pos_lowerBound_b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:28:25.291424+00:00
-- url     : https://prove2.me/theorems/166ffece-dc7a-42dd-988b-c66c076f707b
-- title:
--   Equation (21), Lemma 3 proof — under Axioms 5 and 6, b has a positive lower bound b* on the unit sphere
-- statement:
--   In the conditional logit model, let
--   $$b(\gamma) = \max_{n=1,\dots,N}\ \max_{i,j=1,\dots,J_n} S_{in}(z_{jn} - z_{in})\gamma$$
--   as in Equation (21). Under the standing Axiom 5, if Axiom 6 holds, there is a constant $b^* > 0$ such that $b^* \le b(\gamma)$ for every $\gamma$ in the unit sphere $A = \{\gamma : \gamma'\gamma = 1\}$.
--
--   The constant $b^*$ gives the linear rate at which the log-likelihood decreases in every direction, which makes the maximization problem coercive.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 116 (PDF p. 12), Lemma 3, proof, Equation (21)

import Mathlib
import Definitions.Def_McFadden1974_MLE_Model
import Definitions.Def_McFadden1974_MLE_Axioms

namespace McFadden1974.MLE

open scoped RealInnerProductSpace

/-- **Equation (21) and the bound `b*`** (Lemma 3, proof; McFadden, *Conditional Logit Analysis of Qualitative Choice Behavior*, in P. Zarembka (ed.),
*Frontiers in Econometrics*, Academic Press (1974), p. 116, PDF p. 12):
"Next suppose that Axiom 6 holds. Define A = {γ | γ'γ = 1}. … Define (21)
b(γ) = Max_n Max_{i,j} S_in(z_jn − z_in)γ. Then b is a positive continuous function on the
compact set A, and has a positive lower bound b* on this set."

Under the standing Axiom 5 and Axiom 6 there is `b* > 0` with `b* ≤ b(γ)` for every unit
vector `γ`. -/
theorem exists_pos_lowerBound_b
    {K : ℕ} (d : Data K) (h5 : d.Axiom5) (h6 : d.Axiom6) :
    ∃ bstar : ℝ, 0 < bstar ∧ ∀ γ : EuclideanSpace ℝ (Fin K), ‖γ‖ = 1 → bstar ≤ d.b γ := by sorry

end McFadden1974.MLE
