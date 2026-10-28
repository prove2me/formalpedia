-- Prove2me | Theorems.Thm_OAI_SharpNodal_Profiles_normalized_small_potential_length
-- name    : OAI.SharpNodal.Profiles.normalized_small_potential_length
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:12:19.566275+00:00
-- url     : https://prove2.me/theorems/f6fbef68-8510-415a-88e9-e7656e7e161a
-- title:
--   OAI.SharpNodal.Profiles.normalized_small_potential_length: intermediate lemma from OpenAI, Sharp nodal length on smooth surfaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpNodal.Main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp nodal length on smooth surfaces*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpNodal.Profiles.normalized_small_potential_length` of [lean/OAI/Analysis/NodalLength/NodalLength/LocalLength.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NodalLength/NodalLength/LocalLength.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpNodal.Profiles`, with `open scoped ContDiff Bundle ENNReal`, `open Bundle Manifold MeasureTheory`, `open scoped ContDiff ENNReal Topology`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory Laplacian`, `open scoped Topology ENNReal ContDiff ComplexConjugate`, `open Filter Set MeasureTheory Laplacian`, `open scoped Topology ENNReal ContDiff ComplexConjugate`, `open Filter Set MeasureTheory Laplacian`, `open scoped Topology ENNReal NNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Set MeasureTheory Filter`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Laplacian`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff CompactlySupported`, `open Set MeasureTheory`, `open scoped Topology ENNReal ContDiff CompactlySupported`, `open Set MeasureTheory`, `open scoped Topology ENNReal ContDiff CompactlySupported`, `open Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Laplacian`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory Function`, `open scoped Topology`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped BigOperators`, `open Filter Set MeasureTheory`, `open scoped BigOperators`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff BigOperators`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff BigOperators`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped BigOperators`, `open MeasureTheory`, `open scoped BigOperators`, `open Set MeasureTheory`, `open scoped BigOperators`, `open scoped Classical`, `open scoped BigOperators Topology ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped BigOperators Classical Topology`, `open Filter Set MeasureTheory`, `open scoped BigOperators Classical Topology`, `open Filter Set MeasureTheory`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators Topology`, `open Set MeasureTheory`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators symmDiff`, `open Set`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators symmDiff`, `open Set`, `open scoped BigOperators Classical`, `open Set`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators Classical`, `open Set`, `open scoped BigOperators Classical`, `open Set`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory ComplexConjugate`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory ComplexConjugate`, `open scoped Topology NNReal BoundedContinuousFunction`, `open Filter Set Metric`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ComplexConjugate BigOperators`, `open Filter Set Metric Complex MeromorphicOn`, `open scoped Topology ComplexConjugate BigOperators`, `open Filter Set Metric Complex MeromorphicOn`, `open scoped Topology ComplexConjugate BigOperators`, `open Filter Set Metric Complex`, `open scoped Topology ContDiff ENNReal`, `open Set MeasureTheory Metric`, `open scoped Topology`, `open Set Metric`, `open scoped Topology ComplexConjugate BigOperators`, `open Filter Set Metric Complex MeromorphicOn`, `open scoped Topology`, `open Set Metric Complex`, `open scoped Topology`, `open Set Metric`, `open scoped Topology ContDiff ENNReal`, `open Set MeasureTheory Metric`, `open scoped Topology`, `open Set Metric Complex MeasureTheory`, `open scoped ENNReal Topology`, `open Set Metric MeasureTheory TopologicalSpace Function`, `open scoped Topology ENNReal`, `open Set Metric MeasureTheory Filter`, `open scoped Topology ENNReal`, `open Set Metric MeasureTheory Filter`, `open scoped Topology ENNReal`, `open Set Metric MeasureTheory`, `open scoped Topology ComplexConjugate BigOperators ENNReal`, `open Filter Set Metric Complex MeasureTheory MeromorphicOn`, `open scoped Topology ContDiff Convolution ENNReal`, `open Filter Set MeasureTheory Metric`, `open scoped Topology ContDiff NNReal ENNReal`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff NNReal ENNReal`, `open Filter Set Metric MeasureTheory`, `open Carleman`):
--
--   ```lean
--   theorem normalized_small_potential_length : ∃L : ℝ,0<L ∧
--       ∀{C ε δ : ℝ} {q : Plane → ℝ},SmallPotential C ε δ q →
--       Real.exp (8*C*(4*δ/(1-δ)))-1≤1/2048 →
--       ∀{U : Plane → ℝ},Smooth U →
--       (∀x∈ball (0:Plane) (5/2),euclideanLaplacian U x+q x*U x=0) →
--       ∀S : ℝ,1≤S → (∀x∈ball (0:Plane) (5/2),|U x|≤S) →
--       (∃y∈ball (0:Plane) (1/4),1≤|U y|) →
--       Measure.hausdorffMeasure 1 {x | x∈ball (0:Plane) (1/60) ∧ U x=0}≤
--         ENNReal.ofReal (L*(1+Real.log S))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpNodal.Carleman.Smooth`, `OAI.SharpNodal.Carleman.euclideanLaplacian` and `OAI.SharpNodal.Profiles.SmallPotential` (definitions bundle `OAIQ4Nl000` of this split); `OAI.SharpNodal.Plane` (the published bundle `Def_NodalLength`).
--
--   **Used by.** The proof of `OAI.SharpNodal.Profiles.uniform_plane_length` of this split imports it.
-- source:
--   OpenAI, Sharp nodal length on smooth surfaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-nodal-length-on-smooth-surfaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NodalLength/NodalLength/LocalLength.lean (declaration OAI.SharpNodal.Profiles.normalized_small_potential_length)

import Mathlib
import Definitions.Def_NodalLength
import Definitions.Def_OAIQ4Nl000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory

namespace SharpNodal.Profiles
open Carleman

theorem normalized_small_potential_length : ∃L : ℝ,0<L ∧
    ∀{C ε δ : ℝ} {q : Plane → ℝ},SmallPotential C ε δ q →
    Real.exp (8*C*(4*δ/(1-δ)))-1≤1/2048 →
    ∀{U : Plane → ℝ},Smooth U →
    (∀x∈ball (0:Plane) (5/2),euclideanLaplacian U x+q x*U x=0) →
    ∀S : ℝ,1≤S → (∀x∈ball (0:Plane) (5/2),|U x|≤S) →
    (∃y∈ball (0:Plane) (1/4),1≤|U y|) →
    Measure.hausdorffMeasure 1 {x | x∈ball (0:Plane) (1/60) ∧ U x=0}≤
      ENNReal.ofReal (L*(1+Real.log S)) := by
  sorry
end SharpNodal.Profiles

end

end OAI
end
