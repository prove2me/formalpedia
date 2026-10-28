-- Prove2me | Theorems.Thm_OAI_ContinuousCircleWeight_borel_weight_transport
-- name    : OAI.ContinuousCircleWeight.borel_weight_transport
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T22:08:18.004579+00:00
-- url     : https://prove2.me/theorems/c4caf76f-603d-4dcc-aa7a-207b16b28f67
-- title:
--   OAI.ContinuousCircleWeight.borel_weight_transport: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContinuousCircleWeight.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContinuousCircleWeight.borel_weight_transport` of [lean/OAI/Analysis/RotationWeights/BorelTransport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RotationWeights/BorelTransport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContinuousCircleWeight`, with `open MeasureTheory`, `open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators`, `open MeasureTheory Filter Set Submodule`, `open scoped ENNReal NNReal Topology ComplexInnerProductSpace`, `open MeasureTheory Filter Set`, `open scoped ENNReal NNReal Topology ComplexInnerProductSpace`, `open MeasureTheory Filter Set`, `open scoped ENNReal NNReal Topology ComplexInnerProductSpace`, `open MeasureTheory Filter Set`, `open scoped ENNReal NNReal Topology ComplexInnerProductSpace`, `open MeasureTheory Filter Set`, `open scoped ENNReal NNReal Topology ComplexInnerProductSpace`, `open MeasureTheory Filter Set`, `open scoped ComplexInnerProductSpace`, `open MeasureTheory Filter Set`, `open Set`, `open scoped ComplexInnerProductSpace`, `open Set`, `open scoped ComplexInnerProductSpace`, `open Filter Set`, `open scoped Topology`):
--
--   ```lean
--   theorem borel_weight_transport (θ : ℝ) (f F : RealBorel) (a : CircleX → ℝ)
--       (ha : Measurable a) (hp : ∀ x,0<a x)
--       (he : ∀ᵐ x ∂AddCircle.haarAddCircle,f x*a (x+(θ:CircleX))=F x*a x)
--       (p : CircleFiberOperator) (hproj : IsStarProjection p)
--       (hpc : ∀ B∈fiberCommutant θ,Commute p B) (hp0 : p≠0) (hp1 : p≠1)
--       (hinv : (1-p)*(fiberShiftL2 1*realPi (θ:CircleX) f)*p=0) :
--       ∃ q : CircleFiberOperator,IsStarProjection q ∧ (∀ B∈fiberCommutant θ,Commute q B) ∧
--         q≠0 ∧ q≠1 ∧ (1-q)*(fiberShiftL2 1*realPi (θ:CircleX) F)*q=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContinuousCircleWeight.CircleFiberL2`, `OAI.ContinuousCircleWeight.CircleFiberOperator`, `OAI.ContinuousCircleWeight.FiberHilbert`, `OAI.ContinuousCircleWeight.RealBorel`, `OAI.ContinuousCircleWeight.fiberCommutant`, `OAI.ContinuousCircleWeight.fiberShiftL2` and `OAI.ContinuousCircleWeight.realPi` (definitions bundle `OAIQ2Rw001` of this split); `OAI.ContinuousCircleWeight.CircleX` (the published bundle `Def_ContinuousCircleWeight`).
--
--   **Used by.** The proof of `OAI.ContinuousCircleWeight.main_theorem` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RotationWeights/BorelTransport.lean (declaration OAI.ContinuousCircleWeight.borel_weight_transport)

import Mathlib
import Definitions.Def_ContinuousCircleWeight
import Definitions.Def_OAIQ2Rw001

section

attribute [-instance] _root_.OAI.ContinuousCircleWeight.fiberSeparable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace

open Filter Set
open scoped Topology

theorem borel_weight_transport (θ : ℝ) (f F : RealBorel) (a : CircleX → ℝ)
    (ha : Measurable a) (hp : ∀ x,0<a x)
    (he : ∀ᵐ x ∂AddCircle.haarAddCircle,f x*a (x+(θ:CircleX))=F x*a x)
    (p : CircleFiberOperator) (hproj : IsStarProjection p)
    (hpc : ∀ B∈fiberCommutant θ,Commute p B) (hp0 : p≠0) (hp1 : p≠1)
    (hinv : (1-p)*(fiberShiftL2 1*realPi (θ:CircleX) f)*p=0) :
    ∃ q : CircleFiberOperator,IsStarProjection q ∧ (∀ B∈fiberCommutant θ,Commute q B) ∧
      q≠0 ∧ q≠1 ∧ (1-q)*(fiberShiftL2 1*realPi (θ:CircleX) F)*q=0 := by
  sorry

end ContinuousCircleWeight

end

end OAI
end
