-- Prove2me | Theorems.Thm_OAI_TotientAsymptotic_small_terminal_row_count
-- name    : OAI.TotientAsymptotic.small_terminal_row_count
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:37:22.791742+00:00
-- url     : https://prove2.me/theorems/95895b40-1d66-460b-82ef-91a71b5ca2b6
-- title:
--   OAI.TotientAsymptotic.small_terminal_row_count: intermediate lemma from OpenAI, An asymptotic formula for the number of totients (result family 024)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TotientAsymptotic.coefficient_nonnegative`, `OAI.TotientAsymptotic.totient_asymptotic_formula`, `OAI.TotientAsymptotic.weighted_totient_asymptotic` and `OAI.TotientAsymptotic.weighted_totient_one_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An asymptotic formula for the number of totients (result family 024)*, OpenAI Math Release, September 25, 2026, result family 24, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TotientAsymptotic.small_terminal_row_count` of [lean/OAI/NumberTheory/TotientAsymptotic/SmallTerminalCount.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/SmallTerminalCount.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TotientAsymptotic`, with `open scoped BigOperators Topology`, `open Filter`):
--
--   ```lean
--   theorem small_terminal_row_count : ∃ C : ℝ,0 < C ∧
--       ∀ᶠ x : ℝ in atTop,∀ j : ℕ,1 ≤ j → j ≤ m x →
--       ∀ Q : Finset ℕ,∀ n : ℕ → ℕ,
--       (∀ v ∈ Q,0 < n v ∧ (n v).totient=v ∧ x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧
--         (v:ℝ) ≤ x ∧ 2 < fordPrimeCoordinate (n v) (j-1) ∧
--         fordPrimeCoordinate (n v) j ≤ 2 ∧
--         (∀ i < j,fordRowSum (m x) (fordPrimeCoordinate (n v)) i ≤
--           xi x i*(if i=0 then B x else fordPrimeCoordinate (n v) i))) →
--       (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-((m x-j:ℕ):ℝ)^2/4)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TotientAsymptotic.fordPrime`, `OAI.TotientAsymptotic.fordPrimeCoordinate`, `OAI.TotientAsymptotic.fordRowSum` and `OAI.TotientAsymptotic.xi` (definitions bundle `OAIQ233A000` of this split); `OAI.TotientAsymptotic.B`, `OAI.TotientAsymptotic.G` and `OAI.TotientAsymptotic.m` (the published bundle `Def_TotientAsymptotic`).
--
--   **Used by.** The proof of `OAI.TotientAsymptotic.ford_structure_value_count` of this split imports it.
-- source:
--   OpenAI, An asymptotic formula for the number of totients (result family 024), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 24; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-asymptotic-formula-for-the-number-of-totients-September-25-2026/An-asymptotic-formula-for-the-number-of-totients-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/SmallTerminalCount.lean (declaration OAI.TotientAsymptotic.small_terminal_row_count)

import Mathlib
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Lemmas
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
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.RingTheory.PowerSeries.Inverse
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
namespace TotientAsymptotic

theorem small_terminal_row_count : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ j : ℕ,1 ≤ j → j ≤ m x →
    ∀ Q : Finset ℕ,∀ n : ℕ → ℕ,
    (∀ v ∈ Q,0 < n v ∧ (n v).totient=v ∧ x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧
      (v:ℝ) ≤ x ∧ 2 < fordPrimeCoordinate (n v) (j-1) ∧
      fordPrimeCoordinate (n v) j ≤ 2 ∧
      (∀ i < j,fordRowSum (m x) (fordPrimeCoordinate (n v)) i ≤
        xi x i*(if i=0 then B x else fordPrimeCoordinate (n v) i))) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-((m x-j:ℕ):ℝ)^2/4) := by
  sorry

end TotientAsymptotic

end

end OAI
end
