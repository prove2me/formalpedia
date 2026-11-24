-- Prove2me | Theorems.Thm_GlobalTheory_HCA_SolSub_contDiff_mul_of_on
-- name    : GlobalTheory.HCA.SolSub.contDiff_mul_of_on
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:58:58.951499+00:00
-- url     : https://prove2.me/theorems/eb481a25-e784-451b-98ff-d229cbf05a39
-- title:
--   Sol Sub: cont Diff mul of on
-- statement:
--   The Sol Sub construction uses the cont Diff mul of on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AestronglyMeasurableExtendByZeroOffSubset.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AestronglyMeasurableExtendByZeroOffSubset.lean#L29-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory GlobalTheory.HCA GlobalTheory.HCA.SolSub
variable {d : ℕ}

theorem GlobalTheory.HCA.SolSub.contDiff_mul_of_on {U : Set (E d)} (hU : IsOpen U) {b φ : E d → ℂ}
    (hb : ContDiffOn ℝ ∞ b U) (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun y => b y * φ y) := by sorry
