-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_cloud_gap_sum
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_gap_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:30.435572+00:00
-- url     : https://prove2.me/theorems/e285a96b-c55e-472b-97ec-7d7b029ec8fa
-- title:
--   Wave Grid Lift Grid: cloud gap sum
-- statement:
--   The Wave Grid Lift Grid construction uses the cloud gap sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/CloudProd.lean#L51-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/CloudProd.lean#L51-L63

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

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_gap_sum (k : ℕ) (lam : ℕ → ℝ) (g : ℝ)
    (hgap : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + g ≤ lam s) (s : ℕ) (hs : 1 ≤ s) :
    ∀ s', s ≤ s' → s' ≤ k - 1 → lam s' + ((s' : ℝ) - s) * g ≤ lam s := by sorry
