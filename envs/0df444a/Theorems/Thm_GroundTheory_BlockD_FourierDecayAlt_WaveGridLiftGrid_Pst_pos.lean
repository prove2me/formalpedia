-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_Pst_pos
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst_pos
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:50.383049+00:00
-- url     : https://prove2.me/theorems/25255592-bd79-49be-a20d-5cb5517570f8
-- title:
--   Wave Grid Lift Grid: Pst pos
-- statement:
--   The Wave Grid Lift Grid construction uses the Pst pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/PairOKOfInterlace.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/PairOKOfInterlace.lean#L9-L11

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PairOKOfInterlace
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

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst_pos (k r : ℕ) (lam : ℕ → ℝ) {c : ℝ} (hc : 0 < c) (Y : ℝ) : 0 < Pst k r lam c Y := by sorry
