-- Prove2me | Theorems.Thm_GlobalTheory_mvPowerSeries_variables_syzygy_socle
-- name    : GlobalTheory.mvPowerSeries_variables_syzygy_socle
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:08.169819+00:00
-- url     : https://prove2.me/theorems/8be0e35b-55ad-4124-a91f-296470511b09
-- title:
--   Global Theory: mv Power Series variables syzygy socle
-- statement:
--   The Global Theory construction uses the mv Power Series variables syzygy socle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MvPowerSeriesVariablesSyzygySocle.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MvPowerSeriesVariablesSyzygySocle.lean#L108-L112

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

theorem GlobalTheory.mvPowerSeries_variables_syzygy_socle :
    ∀ (k : Type) [Field k] (g : ℕ) (x : Fin g → MvPowerSeries (Fin g) k), (∀ i, x i = MvPowerSeries.X i) → (∀ r : Fin g → _, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) _, s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x) ∧ ∀ N : ℕ, ∏ i, x i ^ N ∉ Ideal.span (Set.range fun i => x i ^ (N + 1)) := by sorry
