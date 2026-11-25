-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_bracket_const_le
-- name    : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.bracket_const_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:47:38.493245+00:00
-- url     : https://prove2.me/theorems/459511ca-5680-4aa5-9960-42964c0132d4
-- title:
--   Wave Grid Lift Grid: bracket const le
-- statement:
--   The Wave Grid Lift Grid construction uses the bracket const le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/PstMul.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/PstMul.lean#L9-L21

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

theorem GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.bracket_const_le (k r : ℕ) (c b : ℝ) (hc : 0 ≤ c) (hb : 3 ≤ b) (hkb : (k : ℝ) ≤ b)
    (hcb : c + 2 ≤ b) :
    (2 + c) ^ 2 * (k : ℝ) ^ 2 * (3 * b) ^ (2 * r + 3) ≤ b ^ (4 * r + 10) := by sorry
