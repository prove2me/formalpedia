-- Prove2me | Theorems.Thm_OAI_SharpNodal_Geometry_IsConformal_uniform_chart_wave
-- name    : OAI.SharpNodal.Geometry.IsConformal.uniform_chart_wave
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:10:55.912054+00:00
-- url     : https://prove2.me/theorems/6b2128d0-1390-41e9-bdbb-c88fffc53460
-- title:
--   OAI.SharpNodal.Geometry.IsConformal.uniform_chart_wave: intermediate lemma from OpenAI, Sharp nodal length on smooth surfaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpNodal.Main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp nodal length on smooth surfaces*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpNodal.Geometry.IsConformal.uniform_chart_wave` of [lean/OAI/Analysis/NodalLength/NodalLength/ChartTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NodalLength/NodalLength/ChartTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpNodal.Geometry`, with `open scoped ContDiff Bundle ENNReal`, `open Bundle Manifold MeasureTheory`, `open scoped ContDiff ENNReal Topology`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory Laplacian`, `open scoped Topology ENNReal ContDiff ComplexConjugate`, `open Filter Set MeasureTheory Laplacian`, `open scoped Topology ENNReal ContDiff ComplexConjugate`, `open Filter Set MeasureTheory Laplacian`, `open scoped Topology ENNReal NNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Set MeasureTheory Filter`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Laplacian`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff CompactlySupported`, `open Set MeasureTheory`, `open scoped Topology ENNReal ContDiff CompactlySupported`, `open Set MeasureTheory`, `open scoped Topology ENNReal ContDiff CompactlySupported`, `open Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Laplacian`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory Function`, `open scoped Topology`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped BigOperators`, `open Filter Set MeasureTheory`, `open scoped BigOperators`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff BigOperators`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff BigOperators`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped BigOperators`, `open MeasureTheory`, `open scoped BigOperators`, `open Set MeasureTheory`, `open scoped BigOperators`, `open scoped Classical`, `open scoped BigOperators Topology ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped BigOperators Classical Topology`, `open Filter Set MeasureTheory`, `open scoped BigOperators Classical Topology`, `open Filter Set MeasureTheory`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators Topology`, `open Set MeasureTheory`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators symmDiff`, `open Set`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators symmDiff`, `open Set`, `open scoped BigOperators Classical`, `open Set`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators Classical`, `open Set`, `open scoped BigOperators Classical`, `open Set`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory ComplexConjugate`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory ComplexConjugate`, `open scoped Topology NNReal BoundedContinuousFunction`, `open Filter Set Metric`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ComplexConjugate BigOperators`, `open Filter Set Metric Complex MeromorphicOn`, `open scoped Topology ComplexConjugate BigOperators`, `open Filter Set Metric Complex MeromorphicOn`, `open scoped Topology ComplexConjugate BigOperators`, `open Filter Set Metric Complex`, `open scoped Topology ContDiff ENNReal`, `open Set MeasureTheory Metric`, `open scoped Topology`, `open Set Metric`, `open scoped Topology ComplexConjugate BigOperators`, `open Filter Set Metric Complex MeromorphicOn`, `open scoped Topology`, `open Set Metric Complex`, `open scoped Topology`, `open Set Metric`, `open scoped Topology ContDiff ENNReal`, `open Set MeasureTheory Metric`, `open scoped Topology`, `open Set Metric Complex MeasureTheory`, `open scoped ENNReal Topology`, `open Set Metric MeasureTheory TopologicalSpace Function`, `open scoped Topology ENNReal`, `open Set Metric MeasureTheory Filter`, `open scoped Topology ENNReal`, `open Set Metric MeasureTheory Filter`, `open scoped Topology ENNReal`, `open Set Metric MeasureTheory`, `open scoped Topology ComplexConjugate BigOperators ENNReal`, `open Filter Set Metric Complex MeasureTheory MeromorphicOn`, `open scoped Topology ContDiff Convolution ENNReal`, `open Filter Set MeasureTheory Metric`, `open scoped Topology ContDiff NNReal ENNReal`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff NNReal ENNReal`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory Metric`, `open scoped Topology ContDiff ENNReal`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set Metric`, `open scoped Matrix`, `open scoped Topology ContDiff`, `open Filter Set Metric`, `open scoped Topology ContDiff Bundle`, `open Filter Set Metric Bundle Manifold`, `open scoped Topology ContDiff Bundle`, `open Filter Set Metric Bundle Manifold`, `open scoped Topology ContDiff`, `open Filter Set Metric`, `open scoped Topology ContDiff Bundle`, `open Filter Set Metric Bundle Manifold`, `open scoped Topology ContDiff Bundle`, `open Filter Set Metric Bundle Manifold`, `open scoped Topology ContDiff Bundle`, `open Filter Set Metric Bundle Manifold`, `open scoped Topology ContDiff Bundle`, `open Filter Set Metric Bundle Manifold`, `open scoped Topology ContDiff Bundle`, `open Filter Set Metric Bundle Manifold`, `open scoped Topology ContDiff Bundle`, `open Filter Set Metric Bundle Manifold`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory Metric`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory Metric`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory Metric`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory Metric TopologicalSpace`, `open scoped Topology ContDiff ENNReal Bundle`, `open Set Filter MeasureTheory Metric Bundle Manifold`, `open scoped Topology ContDiff ENNReal Bundle`, `open Set Filter MeasureTheory Metric Bundle Manifold`, `open scoped Topology ContDiff ENNReal`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff ENNReal Bundle`, `open Set Filter Metric MeasureTheory Bundle Manifold`, `open scoped Topology ContDiff ENNReal Bundle`, `open Set Filter MeasureTheory Metric Bundle Manifold`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff Bundle`, `open Set Filter Metric Bundle Manifold`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped Topology`, `open Set Filter Metric`, `open scoped Topology ContDiff ENNReal Bundle`, `open Set Filter MeasureTheory Metric Bundle Manifold`, `open scoped Topology ContDiff ENNReal NNReal Bundle Manifold`, `open Set Filter Metric MeasureTheory Bundle Manifold`, `open scoped Topology ContDiff ENNReal NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff ENNReal BigOperators`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff ENNReal NNReal BigOperators`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff ENNReal BigOperators`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff ENNReal`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff ENNReal Bundle`, `open Set Filter Metric MeasureTheory Bundle Manifold`, `open Profiles Carleman`):
--
--   ```lean
--   lemma IsConformal.uniform_chart_wave {e : OpenPartialHomeomorph M Plane} (he : IsConformal e)
--       {y : Plane} {R Cp s k₀ : ℝ} (hCp : 0 ≤ Cp) (hs : 0 < s) (hs1 : s ≤ 1)
--       (hsR : 1000*s < R) (hk₀ : 0 < k₀)
--       (hball : ball y R⊆e.target) (hvol : volume (ball y R) ≤ 1)
--       (hp : ∀z∈ball y R,|conformalFactor e z| ≤ Cp)
--       (hpd : ∀i z,z∈ball y R → |coordPartial (conformalFactor e) i z| ≤ Cp) :
--       ∃Cinit : ℝ,∀K : ℝ,k₀ ≤ K → ∀u : M → ℝ,NormalizedEigen K u →
--         ∀a₀ : ℝ,a₀ ≤ s*K → ∃D : ScaledWave Cp a₀,
--           D.U=(u∘e.symm)∘rescaleMap y s ∧ D.K=s*K ∧ D.growth 0 ≤ Cinit ∧
--           ∀z t,0 < t → ball z t⊆ball (0:Plane) 1000 → centeredMass 0 D.U z t≠0
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpNodal.Geometry.IsConformal`, `OAI.SharpNodal.Geometry.NormalizedEigen`, `OAI.SharpNodal.Geometry.conformalFactor`, `OAI.SharpNodal.Profiles.ScaledWave`, `OAI.SharpNodal.Profiles.centeredMass`, `OAI.SharpNodal.Profiles.rescaleMap`, `OAI.SharpNodal.Profiles.UnitWave` and `OAI.SharpNodal.Profiles.UnitWave.growth` (definitions bundle `OAIQ4Nl000` of this split); `OAI.SharpNodal.Plane` and `OAI.SharpNodal.coordPartial` (the published bundle `Def_NodalLength`).
--
--   **Used by.** The proofs of `OAI_SharpNodal_Geometry_exists_normalized_global_length` and `OAI.SharpNodal.Main` of this split import it.
-- source:
--   OpenAI, Sharp nodal length on smooth surfaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-nodal-length-on-smooth-surfaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NodalLength/NodalLength/ChartTransfer.lean (declaration OAI.SharpNodal.Geometry.IsConformal.uniform_chart_wave)

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
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric TopologicalSpace
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal Bundle
open Set Filter Metric MeasureTheory Bundle Manifold
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Bundle
open Set Filter Metric Bundle Manifold
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff ENNReal Bundle
open Set Filter MeasureTheory Metric Bundle Manifold
open scoped Topology ContDiff ENNReal NNReal Bundle Manifold
open Set Filter Metric MeasureTheory Bundle Manifold
open scoped Topology ContDiff ENNReal NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal NNReal BigOperators
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory

noncomputable section
open scoped Topology ContDiff ENNReal Bundle
open Set Filter Metric MeasureTheory Bundle Manifold
namespace SharpNodal.Geometry
open Profiles Carleman
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [CompactSpace M] [ConnectedSpace M]
lemma IsConformal.uniform_chart_wave {e : OpenPartialHomeomorph M Plane} (he : IsConformal e)
    {y : Plane} {R Cp s k₀ : ℝ} (hCp : 0 ≤ Cp) (hs : 0 < s) (hs1 : s ≤ 1)
    (hsR : 1000*s < R) (hk₀ : 0 < k₀)
    (hball : ball y R⊆e.target) (hvol : volume (ball y R) ≤ 1)
    (hp : ∀z∈ball y R,|conformalFactor e z| ≤ Cp)
    (hpd : ∀i z,z∈ball y R → |coordPartial (conformalFactor e) i z| ≤ Cp) :
    ∃Cinit : ℝ,∀K : ℝ,k₀ ≤ K → ∀u : M → ℝ,NormalizedEigen K u →
      ∀a₀ : ℝ,a₀ ≤ s*K → ∃D : ScaledWave Cp a₀,
        D.U=(u∘e.symm)∘rescaleMap y s ∧ D.K=s*K ∧ D.growth 0 ≤ Cinit ∧
        ∀z t,0 < t → ball z t⊆ball (0:Plane) 1000 → centeredMass 0 D.U z t≠0 := by
  sorry
end SharpNodal.Geometry

end
end

end OAI
end
