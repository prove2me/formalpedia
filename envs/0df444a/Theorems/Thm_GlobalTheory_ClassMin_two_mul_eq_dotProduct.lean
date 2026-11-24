-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_two_mul_eq_dotProduct
-- name    : GlobalTheory.ClassMin.two_mul_eq_dotProduct
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:00.624663+00:00
-- url     : https://prove2.me/theorems/30c0dd1e-12fc-448e-8ee4-d30625a4540c
-- title:
--   Class Min: two mul eq dot Product
-- statement:
--   The Class Min construction uses the two mul eq dot Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L185-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L185-L190

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Matrix Filter
open scoped TensorProduct
variable {X : Type*} [AddCommGroup X] {ι : Type*}
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem GlobalTheory.ClassMin.two_mul_eq_dotProduct [Fintype ι] (Q : QuadraticMap ℤ X ℝ) (e : Module.Basis ι ℤ X) (a : X) :
    2 * Q a = (fun i => (e.repr a i : ℝ)) ⬝ᵥ (gram Q e *ᵥ fun i => (e.repr a i : ℝ)) := by sorry
