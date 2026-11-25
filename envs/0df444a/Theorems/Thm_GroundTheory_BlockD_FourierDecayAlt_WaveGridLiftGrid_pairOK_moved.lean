-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_pairOK_moved
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.pairOK_moved
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:48.259391+00:00
-- url     : https://prove2.me/theorems/7f55ef14-031d-57b9-947e-56ba40d90ced
-- title:
--   Wave Grid Lift Grid: pair OK moved
-- statement:
--   The Wave Grid Lift Grid construction uses the pair OK moved property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/PairOKOfInterlace.lean#L23-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/PairOKOfInterlace.lean#L23-L37

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PairOKOfInterlace
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

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.pairOK_moved (k l : ℕ) (lam u v : ℕ → ℝ) (x : ℝ)
    (h : ∀ s, 1 ≤ s → s ≤ k - 1 → lam s + 1 / 2 ≤ u s ∧ u (s + 1) ≤ lam s - 1 / 2)
    (hv : ∀ i, i ≠ l → i ≠ l + 1 → v i = u i)
    (hlow : ∀ s, 1 ≤ s → s < l → x < lam s) (hhigh : ∀ s, l < s → s ≤ k - 1 → lam s ≤ x) :
    PairOK k lam v l x := by sorry
