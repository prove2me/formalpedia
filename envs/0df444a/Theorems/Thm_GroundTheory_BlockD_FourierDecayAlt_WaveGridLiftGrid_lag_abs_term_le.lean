-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_lag_abs_term_le
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.lag_abs_term_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:41.72621+00:00
-- url     : https://prove2.me/theorems/92447bda-8d14-48d0-b945-aacc079c4e7b
-- title:
--   Wave Grid Lift Grid: lag abs term le
-- statement:
--   The Wave Grid Lift Grid construction uses the lag abs term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/LagSum.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/LagSum.lean#L7-L21

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_LagSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.BlockD GroundTheory.BlockD.FourierDecayAlt GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
open Finset

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.lag_abs_term_le {d : ℕ} (y : Fin (d + 1) → ℝ) (h : ∀ i j, i ≠ j → 5 ≤ |y i - y j|)
    (j : Fin (d + 1)) :
    |∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, (y j - y i)⁻¹| ≤ (1 / 5 : ℝ) ^ d := by sorry
