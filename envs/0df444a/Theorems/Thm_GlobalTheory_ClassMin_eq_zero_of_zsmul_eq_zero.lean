-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_eq_zero_of_zsmul_eq_zero
-- name    : GlobalTheory.ClassMin.eq_zero_of_zsmul_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:27:31.16727+00:00
-- url     : https://prove2.me/theorems/3b91f33a-263a-4e23-aba6-8e182c62f9e3
-- title:
--   Class Min: eq zero of zsmul eq zero
-- statement:
--   The Class Min construction uses the eq zero of zsmul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L26-L31

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

theorem GlobalTheory.ClassMin.eq_zero_of_zsmul_eq_zero (hQ : Q.PosDef) {n : ℤ} (hn : n ≠ 0) {x : X} (h : n • x = 0) :
    x = 0 := by sorry
