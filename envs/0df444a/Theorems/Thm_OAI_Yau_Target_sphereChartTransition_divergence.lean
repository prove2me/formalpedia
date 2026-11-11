-- Prove2me | Theorems.Thm_OAI_Yau_Target_sphereChartTransition_divergence
-- name    : OAI.Yau.Target.sphereChartTransition_divergence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:31:37.121005+00:00
-- url     : https://prove2.me/theorems/bb09afb9-37bf-4046-b810-16825c371c86
-- title:
--   OAI.Yau.Target.sphereChartTransition_divergence: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Target.sphereChartTransition_divergence` of [lean/OAI/Geometry/NodalSets/Charts/SphereOperatorInvariance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Charts/SphereOperatorInvariance.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Target`, with `open Manifold Yau.Geometry Yau.Jets Set Filter`, `open scoped ContDiff Topology`):
--
--   ```lean
--   lemma sphereChartTransition_divergence (p q : Base) {x : _root_.OAI.Yau.Jets.Coord}
--       (hx : x ∈ sphereChartTransitionDomain p q) :
--       complexDivergence (sphereCoordFlux A f p) x =
--         (|(jacobian (sphereChartTransition p q) x).det| : ℝ) *
--           complexDivergence (sphereCoordFlux A f q) (sphereChartTransition p q x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.complexDivergence`, `OAI.Yau.Geometry.jacobian` and `OAI.Yau.Jets.Coord` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Target.IntrinsicTensor`, `OAI.Yau.Target.IntrinsicTensorSmooth` and `OAI.Yau.Target.SphereCotangent` (definitions bundle `OAIQ237Ny001` of this split); `OAI.Yau.Target.sphereChartTransition` and `OAI.Yau.Target.sphereChartTransitionDomain` (definitions bundle `OAIQ237Ny002` of this split); `OAI.Yau.Target.sphereCoordFlux` (definitions bundle `OAIQ237Ny004` of this split); `OAI.Yau.Target.Base` (the published bundle `Def_YauCounterexample`).
--
--   **Used by.** The proof of `OAI.Yau.Target.intrinsic_packed_global_sphere_stage` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Charts/SphereOperatorInvariance.lean (declaration OAI.Yau.Target.sphereChartTransition_divergence)

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004

section

attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f)

include hA hs hp hf

lemma sphereChartTransition_divergence (p q : Base) {x : _root_.OAI.Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    complexDivergence (sphereCoordFlux A f p) x =
      (|(jacobian (sphereChartTransition p q) x).det| : ℝ) *
        complexDivergence (sphereCoordFlux A f q) (sphereChartTransition p q x) := by
  sorry

end
end Yau.Target

end OAI
end
