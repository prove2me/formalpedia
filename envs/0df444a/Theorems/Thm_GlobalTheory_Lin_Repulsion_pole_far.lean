-- Prove2me | Theorems.Thm_GlobalTheory_Lin_Repulsion_pole_far
-- name    : GlobalTheory.Lin.Repulsion.pole_far
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:07:17.107541+00:00
-- url     : https://prove2.me/theorems/23ac3274-847d-4244-9da2-b5b1311b9b89
-- title:
--   Repulsion: pole far
-- statement:
--   The Repulsion construction uses the pole far property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/Repulsion.lean#L70-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/Repulsion.lean#L70-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.Repulsion

theorem GlobalTheory.Lin.Repulsion.pole_far {β t : ℝ} (hβ : β < 1) (hβ' : 1 / 2 ≤ β) (h : ¬ ‖(β : ℂ) - (2 + t * I)‖ ≤ 3) (j : ℕ) :
    ‖1 / ((2 : ℂ) + t * I - 1) ^ j‖ ≤ 1 / 2 ^ j := by sorry
