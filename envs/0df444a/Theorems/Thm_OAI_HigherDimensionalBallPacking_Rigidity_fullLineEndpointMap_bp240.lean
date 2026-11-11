-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_fullLineEndpointMap_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.fullLineEndpointMap_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:58:27.258198+00:00
-- url     : https://prove2.me/theorems/ead7e2b2-70ac-4251-916d-8aca58ee3647
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.fullLineEndpointMap_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.fullLineEndpointMap` of [lean/OAI/Geometry/BallPacking/Continuation/ParameterizedImplicit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Continuation/ParameterizedImplicit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter`, `open HolderCompletion`):
--
--   ```lean
--   lemma fullLineEndpointMap_bp240 : ∀ w∈fullLineDomain b p q M δ,
--       fullLineEquation hJs hJ hJc b b₁ p q (1,w)=0 →
--         AffineLineCurve J p q (markedCurve p q w.val)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.AffineLineCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.standardJ`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Ambient`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.COne`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.HMap`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Holder`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.JetAmbient` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.Pairs` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.supportedHolder` (definitions bundle `OAIQ240Bp005` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedCurve` (definitions bundle `OAIQ240Bp011` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.MarkedEscapeNeighborhood`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineDomain`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation` and `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedBoundedDomain` (definitions bundle `OAIQ240Bp017` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.lcdEnd1` and `OAI.HigherDimensionalBallPacking.Rigidity.lcdEnd2` (definitions bundle `OAIQ240Bp021` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedModel` (definitions bundle `OAIQ240Bp024` of this split); `OAI.HigherDimensionalBallPacking.Phase` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.adapted_line_continuation_data_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Continuation/ParameterizedImplicit.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.fullLineEndpointMap)

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp021

section

attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
section

variable {n : ℕ}

variable (b : ContDiffBump (0:ℂ))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcdEnd1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcdEnd2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd6
local instance lcd7_r600481_1 : AddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (lcd3 (n := n) b).toAddCommGroup
local instance lcd8_r600481_1 : Module ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (lcd4 (n := n) b).toModule
local instance lcd9_r600481_1 : AddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (lcd5 (n := n) b).toAddCommGroup
local instance lcd10_r600481_1 : Module ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (lcd6 (n := n) b).toModule
local instance lcd11_r600481_1 : NormedAddCommGroup (ℝ × markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance lcd12_r600481_1 : NormedSpace ℝ (ℝ × markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n)) (b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)
  (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
  {B M δ : ℝ} (hstd : ∀ x,B<‖x‖ →J x=standardJ n) (hδ : 0<δ)
  (he : ∀ w∈markedBoundedDomain p q M δ,MarkedEscapeNeighborhood b p q w B)

include hb₁ hstd hδ he in
lemma fullLineEndpointMap_bp240 : ∀ w∈fullLineDomain b p q M δ,
    fullLineEquation hJs hJ hJc b b₁ p q (1,w)=0 →
      AffineLineCurve J p q (markedCurve p q w.val) := by
  sorry

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end
