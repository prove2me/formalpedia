-- Prove2me | Theorems.Thm_GlobalTheory_mvPowerSeries_prod_X_pow_notMem
-- name    : GlobalTheory.mvPowerSeries_prod_X_pow_notMem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:22.618194+00:00
-- url     : https://prove2.me/theorems/a156eb57-46b2-4bf4-93cf-0524844ae5dd
-- title:
--   Global Theory: mv Power Series prod X pow not Mem
-- statement:
--   The Global Theory construction uses the mv Power Series prod X pow not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MvPowerSeriesVariablesSyzygySocle.lean#L88-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MvPowerSeriesVariablesSyzygySocle.lean#L88-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPowerSeriesVariablesSyzygySocle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open MvPowerSeries Finsupp

theorem GlobalTheory.mvPowerSeries_prod_X_pow_notMem {k : Type} [CommRing k] [Nontrivial k] {g : ℕ} (N : ℕ) :
    ∏ i, (X i : MvPowerSeries (Fin g) k) ^ N ∉
      Ideal.span (Set.range fun i => (X i : MvPowerSeries (Fin g) k) ^ (N + 1)) := by sorry
