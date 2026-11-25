-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_pairOK_of_interlace
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.pairOK_of_interlace
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:52:09.792603+00:00
-- url     : https://prove2.me/theorems/35f4ad39-fa34-4223-b48a-296cc2fc2586
-- title:
--   Wave Grid Lift Grid: pair OK of interlace
-- statement:
--   The Wave Grid Lift Grid construction uses the pair OK of interlace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/PairOKOfInterlace.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/PairOKOfInterlace.lean#L17-L21

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

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.pairOK_of_interlace (k : ℕ) (lam v : ℕ → ℝ) (e : ℕ) (x : ℝ)
    (h : ∀ s, 1 ≤ s → s ≤ k - 1 → lam s + 1 / 2 ≤ v s ∧ v (s + 1) ≤ lam s - 1 / 2) :
    PairOK k lam v e x := by sorry
