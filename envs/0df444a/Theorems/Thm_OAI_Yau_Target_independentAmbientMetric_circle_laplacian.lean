-- Prove2me | Theorems.Thm_OAI_Yau_Target_independentAmbientMetric_circle_laplacian
-- name    : OAI.Yau.Target.independentAmbientMetric_circle_laplacian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:30:43.991428+00:00
-- url     : https://prove2.me/theorems/f38b9a52-7a7d-451a-a368-dd5cd060e42a
-- title:
--   OAI.Yau.Target.independentAmbientMetric_circle_laplacian: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Target.independentAmbientMetric_circle_laplacian` of [lean/OAI/Geometry/NodalSets/Charts/CircleLaplacian.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Charts/CircleLaplacian.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Target`, with `open Manifold Matrix Yau.Geometry`, `open scoped ContDiff Topology`):
--
--   ```lean
--   lemma independentAmbientMetric_circle_laplacian (p : Manifold5) {y : Model}
--       (hy : y ∈ (extChartAt modelWithCorners p).target) :
--       chartLaplacian (independentAmbientMetric A rho hA hp hr hrp)
--         (extChartAt modelWithCorners p) (circleLift f) y =
--       (baseChartDensity rho p.1 y.1)⁻¹ * ∑ i,
--         fderiv ℝ (baseChartFlux A rho f p.1 i) y.1 (EuclideanSpace.basisFun (Fin 4) ℝ i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Target.BaseModel`, `OAI.Yau.Target.baseChartDensity` and `OAI.Yau.Target.circleLift` (definitions bundle `OAIQ237Ny001` of this split); `OAI.Yau.Target.baseChartFlux` and `OAI.Yau.Target.independentAmbientMetric` (definitions bundle `OAIQ237Ny004` of this split); `OAI.Yau.Target.Base`, `OAI.Yau.Target.Manifold5`, `OAI.Yau.Target.Model`, `OAI.Yau.Target.chartLaplacian` and `OAI.Yau.Target.modelWithCorners` (the published bundle `Def_YauCounterexample`).
--
--   **Used by.** The proof of `OAI.Yau.Target.intrinsic_packed_global_sphere_stage` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Charts/CircleLaplacian.lean (declaration OAI.Yau.Target.independentAmbientMetric_circle_laplacian)

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff Topology
noncomputable section
variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)
    (hrad : ∀ x : Base, A x *ᵥ (fun i ↦ (x : AmbientBase) i) = (fun i ↦ (x : AmbientBase) i))
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f)
include hrad hf

lemma independentAmbientMetric_circle_laplacian (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    chartLaplacian (independentAmbientMetric A rho hA hp hr hrp)
      (extChartAt modelWithCorners p) (circleLift f) y =
    (baseChartDensity rho p.1 y.1)⁻¹ * ∑ i,
      fderiv ℝ (baseChartFlux A rho f p.1 i) y.1 (EuclideanSpace.basisFun (Fin 4) ℝ i) := by
  sorry

end
end Yau.Target

end OAI
end
