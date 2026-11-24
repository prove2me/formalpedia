-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_lt_of_min_class
-- name    : GlobalTheory.ClassMin.lt_of_min_class
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:11:36.939977+00:00
-- url     : https://prove2.me/theorems/b6f8260d-a771-4a08-ad92-6458f1013850
-- title:
--   Class Min: lt of min class
-- statement:
--   The Class Min construction uses the lt of min class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L54-L57

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

theorem GlobalTheory.ClassMin.lt_of_min_class (hQ : Q.PosDef) {N n : ℤ} (hn : 2 ≤ n) {a : X}
    (ha : ∀ w, Q a ≤ Q (a + N • w)) {w : X} (hw : (n * N) • w ≠ 0) :
    Q a < Q (a + (n * N) • w) := by sorry
