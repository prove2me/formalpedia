-- Prove2me | Theorems.Thm_OAI_Yau_Target_sphere_resolvent_H1_difference_test_literal
-- name    : OAI.Yau.Target.sphere_resolvent_H1_difference_test_literal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:34:30.264734+00:00
-- url     : https://prove2.me/theorems/da78bb20-9164-4c21-9143-89a0d643ca37
-- title:
--   OAI.Yau.Target.sphere_resolvent_H1_difference_test_literal: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Target.sphere_resolvent_H1_difference_test_literal` of [lean/OAI/Geometry/NodalSets/Charts/SphereDifferenceTestLiteral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Charts/SphereDifferenceTestLiteral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Target`, with `open MeasureTheory Yau.Geometry Set`, `open scoped ContDiff`):
--
--   ```lean
--   theorem sphere_resolvent_H1_difference_test_literal (d : SphereEnergyData) (f : SphereWeightedL2 d)
--       (p : Base) (z : SphereEnergyHilbert d) (eta theta : Yau.Jets.Coord → ℝ)
--       (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
--       (hes : tsupport eta ⊆ realFinCube 4) (r : ℝ) (hr : r ≤ 1)
--       (hts : tsupport theta ⊆ Yau.realCenteredCube 4 r) (i : Fin 4) (h : ℝ) (hh : |h| ≤ 1-r) :
--       let v := fun x ↦ eta x*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
--       let G := fun j x ↦ eta x*(sphereChartDerivativeMap d p j z) x+
--         Yau.coordPartial eta x j*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
--       let phi := fun x ↦ theta x*Yau.realDifferenceQuotient i h v x
--       let Psi := fun j x ↦ theta x*Yau.realDifferenceQuotient i h (G j) x+
--         Yau.coordPartial theta x j*Yau.realDifferenceQuotient i h v x
--       MemLp phi 2 volume ∧ (∀ j : Fin 4, MemLp (Psi j) 2 volume) ∧
--       (∀ j : Fin 4, Integrable (fun x ↦
--         Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*Psi j x)) ∧
--       Integrable (fun x ↦ sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) phi x) ∧
--       (∑ j, ∫ x, Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*Psi j x) =
--         -(∫ x, sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) phi x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Jets.Coord` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.realDifferenceQuotient`, `OAI.Yau.Geometry.realFinCube`, `OAI.Yau.Target.SphereChartCubeL2` and `OAI.Yau.Target.sphereWeightedL2Measurable` (definitions bundle `OAIQ237Ny001` of this split); `OAI.Yau.coordPartial`, `OAI.Yau.Target.SphereEnergyData`, `OAI.Yau.Target.SphereEnergyHilbert`, `OAI.Yau.Target.SphereEnergySmooth`, `OAI.Yau.Target.sphereChartCoordMap`, `OAI.Yau.Target.SphereEnergySmooth.instAddCommGroup`, `OAI.Yau.Target.SphereEnergySmooth.instInnerProductSpace`, `OAI.Yau.Target.SphereEnergySmooth.instModule` and `OAI.Yau.Target.SphereEnergySmooth.instNormedAddCommGroup` (definitions bundle `OAIQ237Ny002` of this split); `OAI.Yau.realCenteredCube` (definitions bundle `OAIQ237Ny003` of this split); `OAI.Yau.Target.SphereWeightedL2`, `OAI.Yau.Target.sphereChartDerivativeMap`, `OAI.Yau.Target.sphereChartFluxZero`, `OAI.Yau.Target.sphereChartForcingZero`, `OAI.Yau.Target.sphereEnergyL2Map`, `OAI.Yau.Target.sphereWeakSolution` and `OAI.Yau.Target.sphereWeightedMeasure` (definitions bundle `OAIQ237Ny004` of this split); `OAI.Yau.Target.Base` (the published bundle `Def_YauCounterexample`).
--
--   **Used by.** The proof of `OAI.Yau.Target.sphere_resolvent_interior_gradient_difference_bound` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Charts/SphereDifferenceTestLiteral.lean (declaration OAI.Yau.Target.sphere_resolvent_H1_difference_test_literal)

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
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
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

local instance sphereDifferenceLiteralMeasurable_r825082_1 : MeasurableSpace Base := borel Base
local instance sphereDifferenceLiteralBorel_r825082_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_resolvent_H1_difference_test_literal (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (p : Base) (z : SphereEnergyHilbert d) (eta theta : Yau.Jets.Coord → ℝ)
    (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (r : ℝ) (hr : r ≤ 1)
    (hts : tsupport theta ⊆ Yau.realCenteredCube 4 r) (i : Fin 4) (h : ℝ) (hh : |h| ≤ 1-r) :
    let v := fun x ↦ eta x*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
    let G := fun j x ↦ eta x*(sphereChartDerivativeMap d p j z) x+
      Yau.coordPartial eta x j*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
    let phi := fun x ↦ theta x*Yau.realDifferenceQuotient i h v x
    let Psi := fun j x ↦ theta x*Yau.realDifferenceQuotient i h (G j) x+
      Yau.coordPartial theta x j*Yau.realDifferenceQuotient i h v x
    MemLp phi 2 volume ∧ (∀ j : Fin 4, MemLp (Psi j) 2 volume) ∧
    (∀ j : Fin 4, Integrable (fun x ↦
      Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*Psi j x)) ∧
    Integrable (fun x ↦ sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) phi x) ∧
    (∑ j, ∫ x, Yau.realDifferenceQuotient i h (sphereChartFluxZero d p (sphereWeakSolution d f) j) x*Psi j x) =
      -(∫ x, sphereChartForcingZero d p f x*Yau.realDifferenceQuotient i (-h) phi x) := by
  sorry

end
end Yau.Target

end OAI
end
