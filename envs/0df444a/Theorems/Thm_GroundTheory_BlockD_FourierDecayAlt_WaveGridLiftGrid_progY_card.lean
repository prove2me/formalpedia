-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_progY_card
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.progY_card
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:25.816661+00:00
-- url     : https://prove2.me/theorems/1ed32b3f-38e3-4dc6-83ee-f98f84acae07
-- title:
--   Wave Grid Lift Grid: prog Y card
-- statement:
--   The Wave Grid Lift Grid construction uses the prog Y card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/ProgYInjective.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/ProgYInjective.lean#L14-L16

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_ProgYInjective
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

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.progY_card (y0 : ℝ) (M : ℕ) : (progY y0 M).card = M := by sorry
