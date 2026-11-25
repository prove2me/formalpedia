-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_progY_cut
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.progY_cut
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:14.330548+00:00
-- url     : https://prove2.me/theorems/b809c59c-ccad-5a58-a5b1-f85a16370a05
-- title:
--   Wave Grid Lift Grid: prog Y cut
-- statement:
--   The Wave Grid Lift Grid construction uses the prog Y cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/ProgYInjective.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/ProgYInjective.lean#L36-L43

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

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.progY_cut (lo hi : ℝ) (M : ℕ) (hlen : 5 * (M : ℝ) ≤ hi - lo) :
    ∀ y ∈ progY (2 - hi) M, (lo + 2 ≤ -y ∧ -y ≤ hi - 2) ∧ (lo + 2 ≤ -(y + 1) ∧ -(y + 1) ≤ hi - 2) := by sorry
