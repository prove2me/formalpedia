-- Prove2me | Theorems.Thm_OAI_SharpNodal_Profiles_Elliptic_normalized_metric_coordinates
-- name    : OAI.SharpNodal.Profiles.Elliptic.normalized_metric_coordinates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:12:45.088276+00:00
-- url     : https://prove2.me/theorems/b7915931-59b1-43fb-94ad-35a42f962471
-- title:
--   OAI.SharpNodal.Profiles.Elliptic.normalized_metric_coordinates: intermediate lemma from OpenAI, Sharp nodal length on smooth surfaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpNodal.Main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp nodal length on smooth surfaces*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpNodal.Profiles.Elliptic.normalized_metric_coordinates` of [lean/OAI/Analysis/NodalLength/NodalLength/MetricFamilies.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NodalLength/NodalLength/MetricFamilies.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpNodal.Profiles.Elliptic`, with `open scoped ContDiff Bundle ENNReal`, `open Bundle Manifold MeasureTheory`, `open scoped ContDiff ENNReal Topology`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ENNReal ContDiff`, `open MeasureTheory Filter Set`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ContDiff`, `open Filter Set`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory TopologicalSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory Laplacian`, `open scoped Topology ENNReal ContDiff ComplexConjugate`, `open Filter Set MeasureTheory Laplacian`, `open scoped Topology ENNReal ContDiff ComplexConjugate`, `open Filter Set MeasureTheory Laplacian`, `open scoped Topology ENNReal NNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Set MeasureTheory Filter`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Laplacian`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal ContDiff CompactlySupported`, `open Set MeasureTheory`, `open scoped Topology ENNReal ContDiff CompactlySupported`, `open Set MeasureTheory`, `open scoped Topology ENNReal ContDiff CompactlySupported`, `open Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Laplacian`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory Function`, `open scoped Topology`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped BigOperators`, `open Filter Set MeasureTheory`, `open scoped BigOperators`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff BigOperators`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped Topology ENNReal ContDiff BigOperators`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped BigOperators`, `open MeasureTheory`, `open scoped BigOperators`, `open Set MeasureTheory`, `open scoped BigOperators`, `open scoped Classical`, `open scoped BigOperators Topology ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators`, `open scoped Topology ENNReal ContDiff`, `open Filter Set MeasureTheory InnerProductSpace`, `open scoped BigOperators Classical Topology`, `open Filter Set MeasureTheory`, `open scoped BigOperators Classical Topology`, `open Filter Set MeasureTheory`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators Topology`, `open Set MeasureTheory`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators symmDiff`, `open Set`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators symmDiff`, `open Set`, `open scoped BigOperators Classical`, `open Set`, `open scoped BigOperators`, `open Set`, `open scoped BigOperators Classical`, `open Set`, `open scoped BigOperators Classical`, `open Set`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory ComplexConjugate`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory ComplexConjugate`, `open scoped Topology NNReal BoundedContinuousFunction`, `open Filter Set Metric`, `open scoped Topology ContDiff`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ContDiff BigOperators`, `open Filter Set MeasureTheory`, `open scoped Topology ComplexConjugate BigOperators`, `open Filter Set Metric Complex MeromorphicOn`, `open scoped Topology ComplexConjugate BigOperators`, `open Filter Set Metric Complex MeromorphicOn`, `open scoped Topology ComplexConjugate BigOperators`, `open Filter Set Metric Complex`, `open scoped Topology ContDiff ENNReal`, `open Set MeasureTheory Metric`, `open scoped Topology`, `open Set Metric`, `open scoped Topology ComplexConjugate BigOperators`, `open Filter Set Metric Complex MeromorphicOn`, `open scoped Topology`, `open Set Metric Complex`, `open scoped Topology`, `open Set Metric`, `open scoped Topology ContDiff ENNReal`, `open Set MeasureTheory Metric`, `open scoped Topology`, `open Set Metric Complex MeasureTheory`, `open scoped ENNReal Topology`, `open Set Metric MeasureTheory TopologicalSpace Function`, `open scoped Topology ENNReal`, `open Set Metric MeasureTheory Filter`, `open scoped Topology ENNReal`, `open Set Metric MeasureTheory Filter`, `open scoped Topology ENNReal`, `open Set Metric MeasureTheory`, `open scoped Topology ComplexConjugate BigOperators ENNReal`, `open Filter Set Metric Complex MeasureTheory MeromorphicOn`, `open scoped Topology ContDiff Convolution ENNReal`, `open Filter Set MeasureTheory Metric`, `open scoped Topology ContDiff NNReal ENNReal`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff NNReal ENNReal`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set MeasureTheory Metric`, `open scoped Topology ContDiff ENNReal`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set Metric MeasureTheory`, `open scoped Topology ContDiff Convolution`, `open Filter Set Metric MeasureTheory`, `open Carleman`):
--
--   ```lean
--   theorem normalized_metric_coordinates (A : Fin 2 → Fin 2 → Plane → ℝ)
--       (hA : ∀i j,Smooth (A i j)) (hA0 : ∀i j,A i j 0=if i=j then 1 else 0) :
--       ∃(t : ℝ) (u v : Plane → ℝ) (e : OpenPartialHomeomorph Plane Plane),
--         0<t ∧ t<1 ∧ Smooth u ∧ ContDiffOn ℝ ∞ v (ball (0:Plane) (1/64)) ∧
--         (e : Plane → Plane)=coordMap u v ∧ (0:Plane)∈e.source ∧
--         e.source⊆ball (0:Plane) (1/128) ∧
--         ContDiffOn ℝ ∞ (e : Plane → Plane) e.source ∧
--         ContDiffOn ℝ ∞ (e.symm : Plane → Plane) e.target ∧
--         (∀x∈ball (0:Plane) (1/128),
--           coordPartial v 0 x= -(∑j:Fin 2,A 1 j (t • x)*coordPartial u j x) ∧
--           coordPartial v 1 x= ∑j:Fin 2,A 0 j (t • x)*coordPartial u j x) ∧
--         (∀x∈ball (0:Plane) (1/128),
--           ∑i:Fin 2,coordPartial (fun y=>∑j:Fin 2,A i j (t • y)*coordPartial u j y) i x=0) ∧
--         (∀x∈ball (0:Plane) (1/128),
--           0 < coordPartial u 0 x*coordPartial v 1 x-coordPartial u 1 x*coordPartial v 0 x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpNodal.Carleman.Smooth` and `OAI.SharpNodal.Profiles.Elliptic.coordMap` (definitions bundle `OAIQ4Nl000` of this split); `OAI.SharpNodal.Plane` and `OAI.SharpNodal.coordPartial` (the published bundle `Def_NodalLength`).
--
--   **Used by.** The proof of `OAI.SharpNodal.Geometry.exists_isothermal_chart` of this split imports it.
-- source:
--   OpenAI, Sharp nodal length on smooth surfaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-nodal-length-on-smooth-surfaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NodalLength/NodalLength/MetricFamilies.lean (declaration OAI.SharpNodal.Profiles.Elliptic.normalized_metric_coordinates)

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

namespace SharpNodal.Profiles
open Carleman
namespace Elliptic

theorem normalized_metric_coordinates (A : Fin 2 → Fin 2 → Plane → ℝ)
    (hA : ∀i j,Smooth (A i j)) (hA0 : ∀i j,A i j 0=if i=j then 1 else 0) :
    ∃(t : ℝ) (u v : Plane → ℝ) (e : OpenPartialHomeomorph Plane Plane),
      0<t ∧ t<1 ∧ Smooth u ∧ ContDiffOn ℝ ∞ v (ball (0:Plane) (1/64)) ∧
      (e : Plane → Plane)=coordMap u v ∧ (0:Plane)∈e.source ∧
      e.source⊆ball (0:Plane) (1/128) ∧
      ContDiffOn ℝ ∞ (e : Plane → Plane) e.source ∧
      ContDiffOn ℝ ∞ (e.symm : Plane → Plane) e.target ∧
      (∀x∈ball (0:Plane) (1/128),
        coordPartial v 0 x= -(∑j:Fin 2,A 1 j (t • x)*coordPartial u j x) ∧
        coordPartial v 1 x= ∑j:Fin 2,A 0 j (t • x)*coordPartial u j x) ∧
      (∀x∈ball (0:Plane) (1/128),
        ∑i:Fin 2,coordPartial (fun y=>∑j:Fin 2,A i j (t • y)*coordPartial u j y) i x=0) ∧
      (∀x∈ball (0:Plane) (1/128),
        0 < coordPartial u 0 x*coordPartial v 1 x-coordPartial u 1 x*coordPartial v 0 x) := by
  sorry

end Elliptic
end SharpNodal.Profiles

end

end OAI
end
