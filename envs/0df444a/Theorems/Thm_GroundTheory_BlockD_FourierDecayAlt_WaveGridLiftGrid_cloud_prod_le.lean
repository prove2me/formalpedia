-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_cloud_prod_le
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_prod_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:35:16.982409+00:00
-- url     : https://prove2.me/theorems/1f2ce336-7ce2-46d1-a064-43f0fd9e6334
-- title:
--   Wave Grid Lift Grid: cloud prod le
-- statement:
--   The Wave Grid Lift Grid construction uses the cloud prod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/CloudProd.lean#L65-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/CloudProd.lean#L65-L146

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

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_prod_le (k : ℕ) (lam : ℕ → ℝ) (c g Y : ℝ) (hk : 1 ≤ k) (hc : 0 ≤ c) (hg : 1 + c ≤ g)
    (hgap : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + g ≤ lam s) :
    ∏ s ∈ Icc 1 (k - 1), (1 + (1 + c) / max |Y + lam s| 1) ≤ (2 + c) ^ 2 * (k : ℝ) ^ 2 := by sorry
