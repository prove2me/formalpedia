-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_mul_map_add_le
-- name    : GlobalTheory.ClassMin.mul_map_add_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:19.269454+00:00
-- url     : https://prove2.me/theorems/88078f2d-ab51-4fbe-9c65-85fe238ac2d9
-- title:
--   Class Min: mul map add le
-- statement:
--   The Class Min construction uses the mul map add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L76-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L76-L84

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
variable {X : Type*} [AddCommGroup X] {Q : QuadraticMap ℤ X ℝ}

theorem GlobalTheory.ClassMin.mul_map_add_le (hQ : ∀ x, 0 ≤ Q x) (j : ℤ) (a b : X) :
    j * Q (a + b) ≤ (j + 1) * Q a + j * (j + 1) * Q b := by sorry
