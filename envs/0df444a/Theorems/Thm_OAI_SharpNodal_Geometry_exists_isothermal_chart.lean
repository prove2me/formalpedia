-- Prove2me | Theorems.Thm_OAI_SharpNodal_Geometry_exists_isothermal_chart
-- name    : OAI.SharpNodal.Geometry.exists_isothermal_chart
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:10:43.735713+00:00
-- url     : https://prove2.me/theorems/4726e47b-f64b-4f15-bfb4-89c81b7460d1
-- title:
--   OAI.SharpNodal.Geometry.exists_isothermal_chart: intermediate lemma from OpenAI, Sharp nodal length on smooth surfaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpNodal.Main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp nodal length on smooth surfaces*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpNodal.Geometry.exists_isothermal_chart` of [lean/OAI/Analysis/NodalLength/NodalLength/Isothermal.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NodalLength/NodalLength/Isothermal.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpNodal.Geometry`, with `open scoped ContDiff Bundle ENNReal`, `open Bundle Manifold MeasureTheory`, `open scoped ContDiff ENNReal Topology`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory Laplacian`, `open scoped Topology ENNReal ContDiff ComplexConjugate`, `open Filter Set MeasureTheory Laplacian`, `open scoped Topology ENNReal ContDiff ComplexConjugate`, `open Filter Set MeasureTheory Laplacian`, `open scoped Topology ENNReal NNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Set MeasureTheory Filter`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Laplacian`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff CompactlySupported`, `open Set MeasureTheory`, `open scoped Topology ENNReal ContDiff CompactlySupported`, `open Set MeasureTheory`, `open scoped Topology ENNReal ContDiff CompactlySupported`, `open Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Laplacian`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory Function`, `open scoped Topology`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped BigOperators`, `open Filter Set MeasureTheory`, `open scoped BigOperators`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff BigOperators`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff BigOperators`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped BigOperators`, `open MeasureTheory`, `open scoped BigOperators`, `open Set MeasureTheory`, `open scoped BigOperators`, `open scoped Classical`, `open scoped BigOperators Topology ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped BigOperators Classical Topology`, `open Filter Set MeasureTheory`, `open scoped BigOperators Classical Topology`, `open Filter Set MeasureTheory`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators Topology`, `open Set MeasureTheory`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators symmDiff`, `open Set`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators symmDiff`, `open Set`, `open scoped BigOperators Classical`, `open Set`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators Classical`, `open Set`, `open scoped BigOperators Classical`, `open Set`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory ComplexConjugate`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory ComplexConjugate`, `open scoped Topology NNReal BoundedContinuousFunction`, `open Filter Set Metric`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ComplexConjugate BigOperators`, `open Filter Set Metric Complex MeromorphicOn`, `open scoped Topology ComplexConjugate BigOperators`, `open Filter Set Metric Complex MeromorphicOn`, `open scoped Topology ComplexConjugate BigOperators`, `open Filter Set Metric Complex`, `open scoped Topology ContDiff ENNReal`, `open Set MeasureTheory Metric`, `open scoped Topology`, `open Set Metric`, `open scoped Topology ComplexConjugate BigOperators`, `open Filter Set Metric Complex MeromorphicOn`, `open scoped Topology`, `open Set Metric Complex`, `open scoped Topology`, `open Set Metric`, `open scoped Topology ContDiff ENNReal`, `open Set MeasureTheory Metric`, `open scoped Topology`, `open Set Metric Complex MeasureTheory`, `open scoped ENNReal Topology`, `open Set Metric MeasureTheory TopologicalSpace Function`, `open scoped Topology ENNReal`, `open Set Metric MeasureTheory Filter`, `open scoped Topology ENNReal`, `open Set Metric MeasureTheory Filter`, `open scoped Topology ENNReal`, `open Set Metric MeasureTheory`, `open scoped Topology ComplexConjugate BigOperators ENNReal`, `open Filter Set Metric Complex MeasureTheory MeromorphicOn`, `open scoped Topology ContDiff Convolution ENNReal`, `open Filter Set MeasureTheory Metric`, `open scoped Topology ContDiff NNReal ENNReal`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff NNReal ENNReal`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory Metric`, `open scoped Topology ContDiff ENNReal`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set Metric`, `open scoped Matrix`, `open scoped Topology ContDiff`, `open Filter Set Metric`, `open scoped Topology ContDiff Bundle`, `open Filter Set Metric Bundle Manifold`, `open scoped Topology ContDiff Bundle`, `open Filter Set Metric Bundle Manifold`, `open scoped Topology ContDiff`, `open Filter Set Metric`, `open scoped Topology ContDiff Bundle`, `open Filter Set Metric Bundle Manifold`, `open scoped Topology ContDiff Bundle`, `open Filter Set Metric Bundle Manifold`, `open scoped Topology ContDiff Bundle`, `open Filter Set Metric Bundle Manifold`, `open scoped Topology ContDiff Bundle`, `open Filter Set Metric Bundle Manifold`, `open Carleman Profiles.Elliptic`):
--
--   ```lean
--   theorem exists_isothermal_chart (x : M) : ∃e : OpenPartialHomeomorph M Plane,
--       x∈e.source ∧ IsConformal e
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpNodal.Geometry.IsConformal` (definitions bundle `OAIQ4Nl000` of this split); `OAI.SharpNodal.Plane` (the published bundle `Def_NodalLength`).
--
--   **Used by.** The proofs of `OAI_SharpNodal_Geometry_exists_normalized_global_length`, `OAI.SharpNodal.Geometry.normalized_frequency_gap`, `OAI.SharpNodal.Geometry.uniform_local_sup_lower` and `OAI.SharpNodal.Main` of this split import it.
-- source:
--   OpenAI, Sharp nodal length on smooth surfaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-nodal-length-on-smooth-surfaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NodalLength/NodalLength/Isothermal.lean (declaration OAI.SharpNodal.Geometry.exists_isothermal_chart)

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
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

theorem exists_isothermal_chart (x : M) : ∃e : OpenPartialHomeomorph M Plane,
    x∈e.source ∧ IsConformal e := by
  sorry

end SharpNodal.Geometry

end

end OAI
end
