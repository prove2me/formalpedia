-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_lt_add_zsmul_of_le_add
-- name    : GlobalTheory.ClassMin.lt_add_zsmul_of_le_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:43.214851+00:00
-- url     : https://prove2.me/theorems/7b8be26c-f2b3-4a63-90d0-6776d87a4f8d
-- title:
--   Class Min: lt add zsmul of le add
-- statement:
--   The Class Min construction uses the lt add zsmul of le add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L33-L45

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

theorem GlobalTheory.ClassMin.lt_add_zsmul_of_le_add (hQ : Q.PosDef) {t : ℝ} (ht : 0 < t) (ν : X →+ ℝ) {a m : X} {n : ℤ}
    (hn : 2 ≤ n) (h : t * Q a + ν a ≤ t * Q (a + m) + ν (a + m)) (hm : m ≠ 0) :
    t * Q a + ν a < t * Q (a + n • m) + ν (a + n • m) := by sorry
