-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_pst_mul_le
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.pst_mul_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:14:53.958972+00:00
-- url     : https://prove2.me/theorems/2b64edea-3b4e-45e9-8bb7-bfd39c296ec8
-- title:
--   Wave Grid Lift Grid: pst mul le
-- statement:
--   The Wave Grid Lift Grid construction uses the pst mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/PstMul.lean#L23-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/PstMul.lean#L23-L55

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PairOKOfInterlace
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_Bracket
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PstMul
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

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.pst_mul_le (k r : ℕ) (lam u v : ℕ → ℝ) (e e' : ℕ) (c g b Y : ℝ) (hk : 2 ≤ k) (hc : 0 ≤ c)
    (hg : 1 + c ≤ g) (hb : 3 ≤ b) (hkb : (k : ℝ) ≤ b) (hcb : c + 2 ≤ b) (hY : |Y| ≤ b)
    (hlam : ∀ s, 1 ≤ s → s ≤ k + 2 * r + 1 → |lam s| ≤ b)
    (hgap : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + g ≤ lam s)
    (hp : PairOK k lam u e (-Y)) (hp' : PairOK k lam v e' (-Y))
    (hden : ∀ i, 1 ≤ i → i ≤ k → 1 ≤ |Y + 1 / 2 + u i|) (hden' : ∀ i, 1 ≤ i → i ≤ k → 1 ≤ |Y + 1 / 2 + v i|) :
    Pst k r lam c Y * Pst k r lam c (Y + 1) ≤
      b ^ (8 * r + 20) * ∏ i ∈ Icc 1 k, (|Y + 1 / 2 + u i| * |Y + 1 / 2 + v i|) := by sorry
