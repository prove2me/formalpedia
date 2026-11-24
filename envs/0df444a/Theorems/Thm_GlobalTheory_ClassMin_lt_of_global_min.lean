-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_lt_of_global_min
-- name    : GlobalTheory.ClassMin.lt_of_global_min
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:11:13.578255+00:00
-- url     : https://prove2.me/theorems/5b9fbc8c-d2c4-4cbf-b313-9eea99ddb2f6
-- title:
--   Class Min: lt of global min
-- statement:
--   The Class Min construction uses the lt of global min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L69-L74

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

theorem GlobalTheory.ClassMin.lt_of_global_min (hQ : Q.PosDef) (ν : X →+ ℝ) {N : ℤ} (hN : 2 ≤ N) {a : X}
    (ha : ∀ x, Q a / N + ν a ≤ Q x / N + ν x) {w : X} (hw : w ≠ 0) :
    Q a / N + ν a < Q (a + N • w) / N + ν (a + N • w) := by sorry
