-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_map_add_zsmul
-- name    : GlobalTheory.ClassMin.map_add_zsmul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:46.523391+00:00
-- url     : https://prove2.me/theorems/5146b3ce-ad29-44c5-904e-fbe54fd7c60f
-- title:
--   Class Min: map add zsmul
-- statement:
--   The Class Min construction uses the map add zsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L19-L24

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

theorem GlobalTheory.ClassMin.map_add_zsmul (Q : QuadraticMap ℤ X ℝ) (a m : X) (n : ℤ) :
    Q (a + n • m) = Q a + n * polar Q a m + n ^ 2 * Q m := by sorry
