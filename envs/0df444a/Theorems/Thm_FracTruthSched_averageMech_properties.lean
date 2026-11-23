-- Prove2me | Theorems.Thm_FracTruthSched_averageMech_properties
-- name    : FracTruthSched.averageMech_properties
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:54:03.289259+00:00
-- url     : https://prove2.me/theorems/32c3b23a-6e00-4886-b886-a81f5a1c4500
-- title:
--   A finite uniform average of feasible truthful mechanisms is feasible and truthful
-- statement:
--   For a nonempty finite index set $A$, let $(x^a,P^a)$, $a\in A$, be mechanisms on the same tasks and domain. If all are feasible and truthful, then their uniform average
--   $$x_{ie}(t)=\frac1{|A|}\sum_{a\in A}x^a_{ie}(t),\qquad P_i(t)=\frac1{|A|}\sum_{a\in A}P^a_i(t)$$
--   is feasible and truthful. This is the final averaging step in the construction of the padded mechanism and in the proof of Claim 2.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Appendix A.1, The padded mechanism and Claim 2, p.24 (linearity of feasibility and incentive inequalities).

import Mathlib
import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_PaddedConstruction

set_option autoImplicit false

/-- Feasibility and truthfulness are preserved by a uniform average over a nonempty finite
family of mechanisms on a common task set and a common domain. -/
theorem FracTruthSched.averageMech_properties {n : ℕ} {τ ι : Type*} [Fintype τ] [Fintype ι] [Nonempty ι]
    (D : (Fin n → τ → ℝ) → Prop) (N : ι → FracMech n τ)
    (hfeas : ∀ a, IsFeasibleOn D (N a)) (htruth : ∀ a, IsTruthfulOn D (N a)) :
    IsFeasibleOn D (averageMech N) ∧ IsTruthfulOn D (averageMech N) := by sorry
