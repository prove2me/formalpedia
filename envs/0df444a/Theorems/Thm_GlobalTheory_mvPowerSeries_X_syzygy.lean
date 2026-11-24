-- Prove2me | Theorems.Thm_GlobalTheory_mvPowerSeries_X_syzygy
-- name    : GlobalTheory.mvPowerSeries_X_syzygy
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:16.416193+00:00
-- url     : https://prove2.me/theorems/7ae9e783-a457-4111-9782-5fb3d38ff2d6
-- title:
--   Global Theory: mv Power Series X syzygy
-- statement:
--   The Global Theory construction uses the mv Power Series X syzygy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MvPowerSeriesVariablesSyzygySocle.lean#L16-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MvPowerSeriesVariablesSyzygySocle.lean#L16-L85

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

theorem GlobalTheory.mvPowerSeries_X_syzygy {k : Type} [CommRing k] {g : ℕ}
    (r : Fin g → MvPowerSeries (Fin g) k) (hr : ∑ i, r i * X i = 0) :
    ∃ s : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k), s.transpose = -s ∧ (∀ i, s i i = 0) ∧
      r = s.mulVec (fun i => X i) := by sorry
