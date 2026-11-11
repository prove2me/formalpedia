-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_fullLineEquation_local_chart_eq_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation_local_chart_eq_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:00:46.820191+00:00
-- url     : https://prove2.me/theorems/54cb9730-3702-422b-a46c-9b8d38206c7b
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation_local_chart_eq_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation_local_chart_eq` of [lean/OAI/Geometry/BallPacking/Continuation/ParameterizedImplicit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Continuation/ParameterizedImplicit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion`, with `open scoped ContDiff Topology`, `open Filter`, `open scoped BoundedContinuousFunction`, `open Set Function`):
--
--   ```lean
--   lemma fullLineEquation_local_chart_eq_bp240 :
--       (fun h => fullLineEquation hJs hJ hJc b b₁ p q (t,w+h)) =ᶠ[𝓝 0]
--         actualMarkedChart (lineHomotopy_slice_contDiff hJs hJ (fullTime_range t))
--           (fullTime_slice_outside hstd (t := t)) b p q w
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy`, `OAI.HigherDimensionalBallPacking.Rigidity.standardJ`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.HMap`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.fullTime` and `OAI.HigherDimensionalBallPacking.Rigidity.fullTime_range` (definitions bundle `OAIQ240Bp001` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedHolder` (definitions bundle `OAIQ240Bp005` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.MarkedEscapeNeighborhood` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation` (definitions bundle `OAIQ240Bp017` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy_slice_contDiff` (definitions bundle `OAIQ240Bp019` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullTime_slice_outside`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf1` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf2` (definitions bundle `OAIQ240Bp020` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf13` (definitions bundle `OAIQ240Bp022` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedModel` (definitions bundle `OAIQ240Bp024` of this split); `OAI.HigherDimensionalBallPacking.Phase` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.fullLineProperPath_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Continuation/ParameterizedImplicit.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation_local_chart_eq)

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp022

section

attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology
open Filter
open scoped BoundedContinuousFunction
open Set Function
section

variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf4
variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
  (b b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf9
local instance glf10_r4ca53c_1 : Module ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (glf6 (n := n) b).toModule
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf11
local instance glf12_r4ca53c_1 : Module ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (glf8 (n := n) b).toModule
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.glf14
variable (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
  {B : ℝ} (hstd : ∀ x,B<‖x‖ →J x=standardJ n)
  {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
  (w : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : MarkedEscapeNeighborhood b p q w.val B)

include hb₁ hstd ht he in
lemma fullLineEquation_local_chart_eq_bp240 :
    (fun h => fullLineEquation hJs hJ hJc b b₁ p q (t,w+h)) =ᶠ[𝓝 0]
      actualMarkedChart (lineHomotopy_slice_contDiff hJs hJ (fullTime_range t))
        (fullTime_slice_outside hstd (t := t)) b p q w := by
  sorry

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end
