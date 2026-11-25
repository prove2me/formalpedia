-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_cloud_weight_prod
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_weight_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:35:03.964431+00:00
-- url     : https://prove2.me/theorems/45b444c9-bb83-57dc-b863-aa69a21e0bcb
-- title:
--   Wave Grid Lift Grid: cloud weight prod
-- statement:
--   The Wave Grid Lift Grid construction uses the cloud weight prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/CloudProd.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/CloudProd.lean#L7-L15

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

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_weight_prod (c : ℝ) (n : ℕ) :
    ∏ j ∈ range (n + 1), (if j = 0 then 2 + c else 1 + 1 / (j : ℝ)) = (2 + c) * (n + 1) := by sorry
