-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_cloud_pair_le
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_pair_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:34:52.682741+00:00
-- url     : https://prove2.me/theorems/5df7c647-f7bc-5763-8c84-e08d7a7ee2b3
-- title:
--   Wave Grid Lift Grid: cloud pair le
-- statement:
--   The Wave Grid Lift Grid construction uses the cloud pair le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/CloudPair.lean#L19-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/CloudPair.lean#L19-L138

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

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_pair_le (k : ℕ) (lam v : ℕ → ℝ) (e : ℕ) (c g b Y ε : ℝ) (hk : 2 ≤ k) (hc : 0 ≤ c) (hg : 1 + c ≤ g)
    (hε : ε = 0 ∨ ε = 1) (hcb : c + 1 ≤ b) (hY : |Y| ≤ b)
    (hlam : ∀ s, 1 ≤ s → s ≤ k - 1 → |lam s| ≤ b)
    (hgap : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + g ≤ lam s)
    (hp : PairOK k lam v e (-Y)) (hden : ∀ i, 1 ≤ i → i ≤ k → 1 ≤ |Y + 1 / 2 + v i|) :
    ∏ s ∈ Icc 1 (k - 1), (|Y + ε + lam s| + c) ≤
      3 * b * (∏ s ∈ Icc 1 (k - 1), (1 + (1 + c) / max |Y + lam s| 1)) *
        ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := by sorry
