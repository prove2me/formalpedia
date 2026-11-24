-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_lt_of_min_class_of_ne_zero
-- name    : GlobalTheory.ClassMin.lt_of_min_class_of_ne_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:11:29.600967+00:00
-- url     : https://prove2.me/theorems/cbbf788c-881d-47ce-8ed2-6711cc7c589a
-- title:
--   Class Min: lt of min class of ne zero
-- statement:
--   The Class Min construction uses the lt of min class of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L59-L62

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

theorem GlobalTheory.ClassMin.lt_of_min_class_of_ne_zero (hQ : Q.PosDef) {N n : ℤ} (hN : N ≠ 0) (hn : 2 ≤ n) {a : X}
    (ha : ∀ w, Q a ≤ Q (a + N • w)) {w : X} (hw : w ≠ 0) : Q a < Q (a + (n * N) • w) := by sorry
