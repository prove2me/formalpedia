-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_progY_sep
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.progY_sep
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:59.975881+00:00
-- url     : https://prove2.me/theorems/60e8a0bc-96ca-4e27-8e56-45a58f40c806
-- title:
--   Wave Grid Lift Grid: prog Y sep
-- statement:
--   The Wave Grid Lift Grid construction uses the prog Y sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/ProgYInjective.lean#L18-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/ProgYInjective.lean#L18-L34

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

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.progY_sep (y0 : ℝ) (M : ℕ) : ∀ y ∈ progY y0 M, ∀ y' ∈ progY y0 M, y ≠ y' → 5 ≤ |y - y'| := by sorry
