-- Prove2me | Theorems.Thm_OAI_Yau_Geometry_LocalCompactWaveData_actual_lattice_gaussian_small_ball
-- name    : OAI.Yau.Geometry.LocalCompactWaveData.actual_lattice_gaussian_small_ball
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:07:20.273121+00:00
-- url     : https://prove2.me/theorems/d51130f6-d7e7-4a6c-9f1a-72a3c065928c
-- title:
--   OAI.Yau.Geometry.LocalCompactWaveData.actual_lattice_gaussian_small_ball: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Geometry.LocalCompactWaveData.actual_lattice_gaussian_small_ball` of [lean/OAI/Geometry/NodalSets/Waves/LatticeGaussianSmallBall.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Waves/LatticeGaussianSmallBall.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Geometry.LocalCompactWaveData`, with `open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory`, `open scoped ContDiff Topology ENNReal RealInnerProductSpace`):
--
--   ```lean
--   theorem actual_lattice_gaussian_small_ball (hUD : U ⊆ D) (hU : IsOpen U)
--       (hUb : Bornology.IsBounded U) {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
--       ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
--         letI := hfin
--         ∀ (seed : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord), x ∈ Q → DifferentiableAt ℝ seed x →
--         ∀ r : ℝ, 0 ≤ r →
--           (gaussianPairs.map (a.latticeSeededJet hUD n hfin seed x)) {y | ‖y‖ ≤ r} ≤
--             ENNReal.ofReal ((12*(Real.sqrt (c/(n:ℝ)))⁻¹*r/Real.sqrt (2*Real.pi))^5)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.JetSpace`, `OAI.Yau.Geometry.LocalCompactWaveData`, `OAI.Yau.Geometry.SourceGrid`, `OAI.Yau.Jets.Coord` and `OAI.Yau.Geometry.LocalCompactWaveData.latticeSeededJet` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Probability.gaussianPairs` (definitions bundle `OAIQ237Ny001` of this split).
--
--   **Used by.** The proof of `OAI.Yau.Geometry.LocalCompactWaveData.lattice_good_event_probability` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Waves/LatticeGaussianSmallBall.lean (declaration OAI.Yau.Geometry.LocalCompactWaveData.actual_lattice_gaussian_small_ball)

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact
import Definitions.Def_OAIQ237Ny000
import Definitions.Def_OAIQ237Ny001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology ENNReal RealInnerProductSpace
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem actual_lattice_gaussian_small_ball (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ (seed : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord), x ∈ Q → DifferentiableAt ℝ seed x →
      ∀ r : ℝ, 0 ≤ r →
        (gaussianPairs.map (a.latticeSeededJet hUD n hfin seed x)) {y | ‖y‖ ≤ r} ≤
          ENNReal.ofReal ((12*(Real.sqrt (c/(n:ℝ)))⁻¹*r/Real.sqrt (2*Real.pi))^5) := by
  sorry

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end
