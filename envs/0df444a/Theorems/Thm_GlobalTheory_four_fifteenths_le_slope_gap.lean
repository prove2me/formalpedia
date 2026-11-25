-- Prove2me | Theorems.Thm_GlobalTheory_four_fifteenths_le_slope_gap
-- name    : GlobalTheory.four_fifteenths_le_slope_gap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:34:43.960053+00:00
-- url     : https://prove2.me/theorems/37464fc9-5af5-4635-b6e2-6f8ce4814670
-- title:
--   Global Theory: four fifteenths le slope gap
-- statement:
--   The Global Theory construction uses the four fifteenths le slope gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FactorizationLeFourFifteenths.lean#L23-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FactorizationLeFourFifteenths.lean#L23-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FactorizationLeFourFifteenths
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory

theorem GlobalTheory.four_fifteenths_le_slope_gap {x : ℝ} (hx : 5 ≤ x) {i : ℕ} (hi : 1 ≤ i) :
    4 / 15 ≤ (1 / (x ^ 2 - 1) + 1 / 2 - 1 / (8 * x ^ i)) - 1 / (x - 1) := by sorry
