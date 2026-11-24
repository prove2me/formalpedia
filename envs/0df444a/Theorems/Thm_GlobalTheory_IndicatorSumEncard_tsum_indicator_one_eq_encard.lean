-- Prove2me | Theorems.Thm_GlobalTheory_IndicatorSumEncard_tsum_indicator_one_eq_encard
-- name    : GlobalTheory.IndicatorSumEncard.tsum_indicator_one_eq_encard
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:37.922801+00:00
-- url     : https://prove2.me/theorems/45f95e49-9e71-4896-88db-7cc444c39464
-- title:
--   Indicator Sum Encard: tsum indicator one eq encard
-- statement:
--   The Indicator Sum Encard construction uses the tsum indicator one eq encard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SetLIntegralLeMulOfEncardLe.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SetLIntegralLeMulOfEncardLe.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SetLIntegralLeMulOfEncardLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.IndicatorSumEncard

theorem GlobalTheory.IndicatorSumEncard.tsum_indicator_one_eq_encard {ι : Type} (A : Set ι) :
    ∑' i : ι, A.indicator (fun _ => (1 : ENNReal)) i = (A.encard : ENNReal) := by sorry
