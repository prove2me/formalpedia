-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_cloud_factor_le
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_factor_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:32.011789+00:00
-- url     : https://prove2.me/theorems/736a95ec-fa22-4d98-8a7f-2a18b7541f71
-- title:
--   Wave Grid Lift Grid: cloud factor le
-- statement:
--   The Wave Grid Lift Grid construction uses the cloud factor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/CloudProd.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/CloudProd.lean#L17-L32

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_CloudProd
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

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_factor_le (c g d : ℝ) (j : ℕ) (hc : 0 ≤ c) (hg : 1 + c ≤ g) (hd : (j : ℝ) * g ≤ d) :
    1 + (1 + c) / max d 1 ≤ (if j = 0 then 2 + c else 1 + 1 / (j : ℝ)) := by sorry
