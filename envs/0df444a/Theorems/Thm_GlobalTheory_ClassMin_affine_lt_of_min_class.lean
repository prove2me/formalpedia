-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_affine_lt_of_min_class
-- name    : GlobalTheory.ClassMin.affine_lt_of_min_class
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:11:29.027842+00:00
-- url     : https://prove2.me/theorems/c2086301-5032-4b41-b87b-ef6ea8d80805
-- title:
--   Class Min: affine lt of min class
-- statement:
--   The Class Min construction uses the affine lt of min class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L47-L52

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

theorem GlobalTheory.ClassMin.affine_lt_of_min_class (hQ : Q.PosDef) {t : ℝ} (ht : 0 < t) (ν : X →+ ℝ) {N n : ℤ}
    (hn : 2 ≤ n) {a : X} (ha : ∀ w, t * Q a + ν a ≤ t * Q (a + N • w) + ν (a + N • w)) {w : X}
    (hw : (n * N) • w ≠ 0) :
    t * Q a + ν a < t * Q (a + (n * N) • w) + ν (a + (n * N) • w) := by sorry
