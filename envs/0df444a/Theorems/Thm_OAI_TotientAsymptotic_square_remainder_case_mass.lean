-- Prove2me | Theorems.Thm_OAI_TotientAsymptotic_square_remainder_case_mass
-- name    : OAI.TotientAsymptotic.square_remainder_case_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:37:32.880201+00:00
-- url     : https://prove2.me/theorems/06f8006c-40ec-4c17-ad79-5cb74d42219e
-- title:
--   OAI.TotientAsymptotic.square_remainder_case_mass: intermediate lemma from OpenAI, An asymptotic formula for the number of totients (result family 024)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TotientAsymptotic.coefficient_nonnegative`, `OAI.TotientAsymptotic.totient_asymptotic_formula`, `OAI.TotientAsymptotic.weighted_totient_asymptotic` and `OAI.TotientAsymptotic.weighted_totient_one_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An asymptotic formula for the number of totients (result family 024)*, OpenAI Math Release, September 25, 2026, result family 24, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TotientAsymptotic.square_remainder_case_mass` of [lean/OAI/NumberTheory/TotientAsymptotic/SquareRemainderLayer.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/SquareRemainderLayer.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TotientAsymptotic`, with `open scoped BigOperators Topology`, `open Filter`):
--
--   ```lean
--   lemma square_remainder_case_mass (hbox : FordUnitPrimeBoxInput)
--       (hren : FordRenewalInput) (hmertens : MertensProductInput) :
--       ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
--         ∀ i j k q : ℕ, 1 ≤ i → i ≤ R x H → i ≤ j → j ≤ L x H →
--         i ≤ k → k ≤ L x H → q.Prime →
--         let b := fordBandScale x i
--         let A := 1+Real.log (discardPrimeBound b : ℝ)
--         (∑ η ∈ squareRemainderCase x H q j k, remainderReciprocalWeight η) ≤
--         (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*G x (m x)*
--           (A^2*(D*(2*b+2))^(m x-i))*((q : ℝ)^2)⁻¹
--   ```
--
--   **Definitions.** The statement is written with `OAI.TotientAsymptotic.FordRenewalInput`, `OAI.TotientAsymptotic.FordUnitPrimeBoxInput`, `OAI.TotientAsymptotic.L`, `OAI.TotientAsymptotic.MertensProductInput`, `OAI.TotientAsymptotic.R`, `OAI.TotientAsymptotic.RemainderDatum`, `OAI.TotientAsymptotic.discardPrimeBound`, `OAI.TotientAsymptotic.fordBandScale`, `OAI.TotientAsymptotic.remainderReciprocalWeight`, `OAI.TotientAsymptotic.squareRemainderCase` and `OAI.TotientAsymptotic.tailCofactorBound` (definitions bundle `OAIQ233A000` of this split); `OAI.TotientAsymptotic.G` and `OAI.TotientAsymptotic.m` (the published bundle `Def_TotientAsymptotic`).
--
--   **Used by.** The proof of `OAI.TotientAsymptotic.bad_tuple_discard` of this split imports it.
-- source:
--   OpenAI, An asymptotic formula for the number of totients (result family 024), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 24; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-asymptotic-formula-for-the-number-of-totients-September-25-2026/An-asymptotic-formula-for-the-number-of-totients-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/SquareRemainderLayer.lean (declaration OAI.TotientAsymptotic.square_remainder_case_mass)

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Log
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
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
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
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma square_remainder_case_mass (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ i j k q : ℕ, 1 ≤ i → i ≤ R x H → i ≤ j → j ≤ L x H →
      i ≤ k → k ≤ L x H → q.Prime →
      let b := fordBandScale x i
      let A := 1+Real.log (discardPrimeBound b : ℝ)
      (∑ η ∈ squareRemainderCase x H q j k, remainderReciprocalWeight η) ≤
      (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*G x (m x)*
        (A^2*(D*(2*b+2))^(m x-i))*((q : ℝ)^2)⁻¹ := by
  sorry

end TotientAsymptotic

end

end OAI
end
