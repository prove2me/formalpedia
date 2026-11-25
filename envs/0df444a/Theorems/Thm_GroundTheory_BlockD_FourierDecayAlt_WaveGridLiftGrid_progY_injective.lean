-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_progY_injective
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.progY_injective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:03:39.756266+00:00
-- url     : https://prove2.me/theorems/911b65a9-7152-54b5-8f90-9465633222c1
-- title:
--   Wave Grid Lift Grid: prog Y injective
-- statement:
--   The Wave Grid Lift Grid construction uses the prog Y injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/ProgYInjective.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/ProgYInjective.lean#L9-L12

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

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.progY_injective (y0 : ℝ) : Function.Injective fun i : ℕ => y0 + 5 * (i : ℝ) := by sorry
