-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_actualMarkedChart_contDiff_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_contDiff_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:57:30.983203+00:00
-- url     : https://prove2.me/theorems/7f1f40c9-13bc-49d8-b277-6774841fd598
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_contDiff_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_contDiff` of [lean/OAI/Geometry/BallPacking/Fredholm/PointwiseMarkedCR.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/PointwiseMarkedCR.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter`):
--
--   ```lean
--   lemma actualMarkedChart_contDiff_bp240 : ContDiff ℝ ∞ (actualMarkedChart hJ hstd b p q u)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.standardJ`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.HMap`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedHolder` (definitions bundle `OAIQ240Bp005` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst7` (definitions bundle `OAIQ240Bp017` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst6` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst8` (definitions bundle `OAIQ240Bp018` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst10` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst9` (definitions bundle `OAIQ240Bp020` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedModel` (definitions bundle `OAIQ240Bp024` of this split); `OAI.HigherDimensionalBallPacking.Phase` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_derivative_eq_linearized_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/PointwiseMarkedCR.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_contDiff)

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp020

section

attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {K : Set ℂ}

variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst8
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) {B : ℝ}
    (hstd : ∀ x, B < ‖x‖ → J x = standardJ n)

variable (b : ContDiffBump (0:ℂ)) (p q : Phase n)

variable (u : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst11
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst12
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst13
lemma actualMarkedChart_contDiff_bp240 : ContDiff ℝ ∞ (actualMarkedChart hJ hstd b p q u) := by
  sorry

end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end
