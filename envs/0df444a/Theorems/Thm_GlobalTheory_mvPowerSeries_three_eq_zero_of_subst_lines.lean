-- Prove2me | Theorems.Thm_GlobalTheory_mvPowerSeries_three_eq_zero_of_subst_lines
-- name    : GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:58:49.916643+00:00
-- url     : https://prove2.me/theorems/80017c5a-d14f-4eb5-931c-98423338db3a
-- title:
--   Global Theory: mv Power Series three eq zero of subst lines
-- statement:
--   The Global Theory construction uses the mv Power Series three eq zero of subst lines property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MvPowerSeriesThreeEqZeroOfSubstLines.lean#L5-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MvPowerSeriesThreeEqZeroOfSubstLines.lean#L5-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MvPowerSeriesThreeEqZeroOfSubstLines
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines :
    ∀ (K : Type) [Field K] [Infinite K] (Φ : MvPowerSeries (Fin 3) K),
      (∀ t : Fin 3 → K, (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ : PowerSeries K) = 0) →
      Φ = 0 := by sorry
