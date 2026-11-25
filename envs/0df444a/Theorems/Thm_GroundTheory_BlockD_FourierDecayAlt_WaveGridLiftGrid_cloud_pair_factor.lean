-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_cloud_pair_factor
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_pair_factor
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:35:15.769661+00:00
-- url     : https://prove2.me/theorems/62180188-3f59-41e2-9279-e9905841d2f4
-- title:
--   Wave Grid Lift Grid: cloud pair factor
-- statement:
--   The Wave Grid Lift Grid construction uses the cloud pair factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/CloudPair.lean#L8-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/CloudPair.lean#L8-L17

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PairOKOfInterlace
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_CloudPair
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

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_pair_factor (a d c D : ℝ) (hc : 0 ≤ c) (ha : a ≤ d + 1 + c) (hD1 : d ≤ D)
    (hD2 : 1 ≤ D) : a ≤ (1 + (1 + c) / max d 1) * D := by sorry
