-- Prove2me | Theorems.Thm_GlobalTheory_HCA_SolSub_integrable_tr
-- name    : GlobalTheory.HCA.SolSub.integrable_tr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:59:54.704594+00:00
-- url     : https://prove2.me/theorems/315920c2-884b-4381-91d8-b98b589cb8bc
-- title:
--   Sol Sub: integrable tr
-- statement:
--   The Sol Sub construction uses the integrable tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AestronglyMeasurableExtendByZeroOffSubset.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AestronglyMeasurableExtendByZeroOffSubset.lean#L43-L53

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

theorem GlobalTheory.HCA.SolSub.integrable_tr {ι : Type} (P : Sys d ι) {U : Set (E d)} (hU : IsOpen U)
    (ha : ∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) (i : ι) {φ : E d → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    Integrable (P.tr i φ) := by sorry
