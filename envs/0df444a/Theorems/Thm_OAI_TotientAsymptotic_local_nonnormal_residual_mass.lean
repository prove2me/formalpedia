-- Prove2me | Theorems.Thm_OAI_TotientAsymptotic_local_nonnormal_residual_mass
-- name    : OAI.TotientAsymptotic.local_nonnormal_residual_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:34:53.794023+00:00
-- url     : https://prove2.me/theorems/0ded53d0-1b49-47ea-9df6-b967399fbfdc
-- title:
--   OAI.TotientAsymptotic.local_nonnormal_residual_mass: intermediate lemma from OpenAI, An asymptotic formula for the number of totients (result family 024)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TotientAsymptotic.coefficient_nonnegative`, `OAI.TotientAsymptotic.totient_asymptotic_formula`, `OAI.TotientAsymptotic.weighted_totient_asymptotic` and `OAI.TotientAsymptotic.weighted_totient_one_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An asymptotic formula for the number of totients (result family 024)*, OpenAI Math Release, September 25, 2026, result family 24, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TotientAsymptotic.local_nonnormal_residual_mass` of [lean/OAI/NumberTheory/TotientAsymptotic/LocalExceptionalResidualMass.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/LocalExceptionalResidualMass.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TotientAsymptotic`, with `open scoped BigOperators Topology`, `open Filter`):
--
--   ```lean
--   theorem local_nonnormal_residual_mass {c A : ℝ} (hc : 0 < c) (hA : 0 < A)
--       (d q L : ℕ) (hd : 0 < d) :
--       ∀ᶠ h : ℕ in atTop,∀ (R Q : Finset ℕ) (F : ℕ → ℕ),Q ⊆ R →
--         (∀ r ∈ Q,∃ p : ℕ,p.Prime ∧ p-1 ≤ d*r.totient ∧
--           c*(rho^h)⁻¹ ≤ B p ∧ ((d*r.totient:ℕ):ℝ) ≤
--             Real.exp (Real.exp (localPrimeHeight A L h))) →
--         (∀ r ∈ R,∀ p : ℕ,p.Prime → p ∣ r → IsNormalPrime (localNormalityScale h) p) →
--         (∀ p : ℕ,p.Prime → p ∣ q → IsNormalPrime (localNormalityScale h) p) →
--         (∀ r ∈ R,(∃ s ∈ R,s≠r ∧ s.totient=r.totient) → ∃ s ∈ R,F r=s*q) →
--         (∀ r ∈ Q,∃ p : ℕ,p.Prime ∧ p ∣ F r ∧ ¬IsNormalPrime (localNormalityScale h) p) →
--         (∀ r ∈ Q,0<F r ∧ (F r).totient=d*r.totient) →
--         (∑ r ∈ Q,(r.totient:ℝ)⁻¹) ≤ rho^h
--   ```
--
--   **Definitions.** The statement is written with `OAI.TotientAsymptotic.IsNormalPrime`, `OAI.TotientAsymptotic.localNormalityScale` and `OAI.TotientAsymptotic.localPrimeHeight` (definitions bundle `OAIQ233A000` of this split); `OAI.TotientAsymptotic.B` and `OAI.TotientAsymptotic.rho` (the published bundle `Def_TotientAsymptotic`).
--
--   **Used by.** The proof of `OAI.TotientAsymptotic.local_bad_suffix_exception_data` of this split imports it.
-- source:
--   OpenAI, An asymptotic formula for the number of totients (result family 024), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 24; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-asymptotic-formula-for-the-number-of-totients-September-25-2026/An-asymptotic-formula-for-the-number-of-totients-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/LocalExceptionalResidualMass.lean (declaration OAI.TotientAsymptotic.local_nonnormal_residual_mass)

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Squarefree
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Bound
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Compact
import Definitions.Def_TotientAsymptotic
import Definitions.Def_OAIQ233A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_nonnormal_residual_mass {c A : ℝ} (hc : 0 < c) (hA : 0 < A)
    (d q L : ℕ) (hd : 0 < d) :
    ∀ᶠ h : ℕ in atTop,∀ (R Q : Finset ℕ) (F : ℕ → ℕ),Q ⊆ R →
      (∀ r ∈ Q,∃ p : ℕ,p.Prime ∧ p-1 ≤ d*r.totient ∧
        c*(rho^h)⁻¹ ≤ B p ∧ ((d*r.totient:ℕ):ℝ) ≤
          Real.exp (Real.exp (localPrimeHeight A L h))) →
      (∀ r ∈ R,∀ p : ℕ,p.Prime → p ∣ r → IsNormalPrime (localNormalityScale h) p) →
      (∀ p : ℕ,p.Prime → p ∣ q → IsNormalPrime (localNormalityScale h) p) →
      (∀ r ∈ R,(∃ s ∈ R,s≠r ∧ s.totient=r.totient) → ∃ s ∈ R,F r=s*q) →
      (∀ r ∈ Q,∃ p : ℕ,p.Prime ∧ p ∣ F r ∧ ¬IsNormalPrime (localNormalityScale h) p) →
      (∀ r ∈ Q,0<F r ∧ (F r).totient=d*r.totient) →
      (∑ r ∈ Q,(r.totient:ℝ)⁻¹) ≤ rho^h := by
  sorry

end TotientAsymptotic

end

end OAI
end
