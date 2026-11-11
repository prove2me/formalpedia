-- Prove2me | Theorems.Thm_OAI_Yau_Geometry_lattice_sign_margin_probability_fixed_domain
-- name    : OAI.Yau.Geometry.lattice_sign_margin_probability_fixed_domain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:27:39.567281+00:00
-- url     : https://prove2.me/theorems/3d474a12-cc00-427e-b94f-a84d3c0d7e0b
-- title:
--   OAI.Yau.Geometry.lattice_sign_margin_probability_fixed_domain: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Geometry.lattice_sign_margin_probability_fixed_domain` of [lean/OAI/Geometry/NodalSets/Waves/FixedDomainLatticeSignMargin.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Waves/FixedDomainLatticeSignMargin.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Geometry`, with `open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory`, `open scoped ContDiff Topology ENNReal`):
--
--   ```lean
--   theorem lattice_sign_margin_probability_fixed_domain
--       (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) {H : Set _root_.OAI.Yau.Jets.Coord}
--       (hH : IsCompact H) (hg : ContinuousOn g H)
--       (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
--       ∃ tau : ℝ, 0 < tau ∧ tau < 1/4 ∧ ∃ p : ℝ≥0∞, 0 < p ∧
--         ∀ (w S S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (D U Q : Set _root_.OAI.Yau.Jets.Coord) (m J K k0 : ℕ)
--           (a : LocalCompactWaveData g w S D m J K k0) (_ : IsCompact D) (_ : D ⊆ H) (hUD : U ⊆ D),
--           U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
--           ContDiff ℝ ∞ S → ContDiff ℝ ∞ S0 → ContDiff ℝ ∞ T0 →
--           ∀ gamma > 0, (∀ x ∈ Q, S0 x+gamma ≤ S x) →
--           ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
--             ∀ x ∈ Q, ∃ j : Fin 4,
--               let F := rescaledGaussianField
--                 (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2)
--                 S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x
--               p ≤ gaussianPairs {coeff | 1 ≤ F coeff 0 ∧ F coeff (tau • Pi.single j 1) ≤ -1}
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.LocalCompactWaveData`, `OAI.Yau.Geometry.SourceGrid`, `OAI.Yau.Geometry.latticeWave`, `OAI.Yau.Geometry.sourceSignScale`, `OAI.Yau.Jets.Coord` and `OAI.Yau.Geometry.LocalCompactWaveData.latticeSigma` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Probability.gaussianPairs` (definitions bundle `OAIQ237Ny001` of this split); `OAI.Yau.Geometry.rescaledGaussianField` (definitions bundle `OAIQ237Ny002` of this split).
--
--   **Used by.** The proof of `OAI.Yau.Geometry.lattice_physical_sign_subballs_fixed_domain` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Waves/FixedDomainLatticeSignMargin.lean (declaration OAI.Yau.Geometry.lattice_sign_margin_probability_fixed_domain)

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
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
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_OAIQ237Ny002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology ENNReal
noncomputable section

theorem lattice_sign_margin_probability_fixed_domain
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) {H : Set _root_.OAI.Yau.Jets.Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ tau : ℝ, 0 < tau ∧ tau < 1/4 ∧ ∃ p : ℝ≥0∞, 0 < p ∧
      ∀ (w S S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (D U Q : Set _root_.OAI.Yau.Jets.Coord) (m J K k0 : ℕ)
        (a : LocalCompactWaveData g w S D m J K k0) (_ : IsCompact D) (_ : D ⊆ H) (hUD : U ⊆ D),
        U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
        ContDiff ℝ ∞ S → ContDiff ℝ ∞ S0 → ContDiff ℝ ∞ T0 →
        ∀ gamma > 0, (∀ x ∈ Q, S0 x+gamma ≤ S x) →
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
          ∀ x ∈ Q, ∃ j : Fin 4,
            let F := rescaledGaussianField
              (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2)
              S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x
            p ≤ gaussianPairs {coeff | 1 ≤ F coeff 0 ∧ F coeff (tau • Pi.single j 1) ≤ -1} := by
  sorry

end
end Yau.Geometry

end OAI
end
