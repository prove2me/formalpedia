-- Prove2me | Theorems.Thm_OAI_TotientAsymptotic_cofactor_sieve_cutoff_mass
-- name    : OAI.TotientAsymptotic.cofactor_sieve_cutoff_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:32:30.859496+00:00
-- url     : https://prove2.me/theorems/45eb0d91-f37a-41f5-88c5-d6fc13e97218
-- title:
--   OAI.TotientAsymptotic.cofactor_sieve_cutoff_mass: intermediate lemma from OpenAI, An asymptotic formula for the number of totients (result family 024)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TotientAsymptotic.coefficient_nonnegative`, `OAI.TotientAsymptotic.totient_asymptotic_formula`, `OAI.TotientAsymptotic.weighted_totient_asymptotic` and `OAI.TotientAsymptotic.weighted_totient_one_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An asymptotic formula for the number of totients (result family 024)*, OpenAI Math Release, September 25, 2026, result family 24, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TotientAsymptotic.cofactor_sieve_cutoff_mass` of [lean/OAI/NumberTheory/TotientAsymptotic/CofactorSieveCutoff.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/CofactorSieveCutoff.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TotientAsymptotic`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma cofactor_sieve_cutoff_mass : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
--       Real.exp 2 ≤ x → 0 < B x → 1 ≤ Real.log x/(200*B x) → ∀ Q : Finset ℕ,
--       (∀ b ∈ Q,0 < b ∧ (b:ℝ)*Real.exp (Real.log x/(100*B x)) ≤ x) →
--       (∑ b ∈ Q,((allShiftedPrimePairs b ⌊x/b⌋₊).card:ℝ)) ≤
--         C*x*(B x)^3/(Real.log x)^2*(∑ b ∈ Q,(b:ℝ)⁻¹)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TotientAsymptotic.allShiftedPrimePairs` (definitions bundle `OAIQ233A000` of this split); `OAI.TotientAsymptotic.B` (the published bundle `Def_TotientAsymptotic`).
--
--   **Used by.** The proof of `OAI.TotientAsymptotic.fordLemma26Input` of this split imports it.
-- source:
--   OpenAI, An asymptotic formula for the number of totients (result family 024), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 24; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-asymptotic-formula-for-the-number-of-totients-September-25-2026/An-asymptotic-formula-for-the-number-of-totients-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/CofactorSieveCutoff.lean (declaration OAI.TotientAsymptotic.cofactor_sieve_cutoff_mass)

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_TotientAsymptotic
import Definitions.Def_OAIQ233A000

section

attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma cofactor_sieve_cutoff_mass : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
    Real.exp 2 ≤ x → 0 < B x → 1 ≤ Real.log x/(200*B x) → ∀ Q : Finset ℕ,
    (∀ b ∈ Q,0 < b ∧ (b:ℝ)*Real.exp (Real.log x/(100*B x)) ≤ x) →
    (∑ b ∈ Q,((allShiftedPrimePairs b ⌊x/b⌋₊).card:ℝ)) ≤
      C*x*(B x)^3/(Real.log x)^2*(∑ b ∈ Q,(b:ℝ)⁻¹) := by
  sorry

end TotientAsymptotic

end

end OAI
end
