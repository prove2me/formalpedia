-- Prove2me | Theorems.Thm_OAI_TotientAsymptotic_ppt_regular_geometric_witness
-- name    : OAI.TotientAsymptotic.ppt_regular_geometric_witness
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:36:38.633086+00:00
-- url     : https://prove2.me/theorems/554dfe65-6498-441d-aa56-a9a108f8f5bc
-- title:
--   OAI.TotientAsymptotic.ppt_regular_geometric_witness: intermediate lemma from OpenAI, An asymptotic formula for the number of totients (result family 024)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TotientAsymptotic.coefficient_nonnegative`, `OAI.TotientAsymptotic.totient_asymptotic_formula`, `OAI.TotientAsymptotic.weighted_totient_asymptotic` and `OAI.TotientAsymptotic.weighted_totient_one_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An asymptotic formula for the number of totients (result family 024)*, OpenAI Math Release, September 25, 2026, result family 24, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TotientAsymptotic.ppt_regular_geometric_witness` of [lean/OAI/NumberTheory/TotientAsymptotic/PPTRegularWitness.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/PPTRegularWitness.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TotientAsymptotic`, with `open scoped BigOperators Topology`, `open Filter`):
--
--   ```lean
--   theorem ppt_regular_geometric_witness (d : ℕ) (hd : 0 < d) {A : ℝ} (hA : 0 < A) :
--       ∀ᶠ z : ℝ in atTop,
--       ∀ (m n N H F r : ℕ) (p : Fin N → ℕ) (v : Fin n → ℝ)
--         (ι : Fin N ↪o Fin n) (budget c S : ℝ),∀ hN : 0 < N,
--         n ≤ m → N ≤ H → (H:ℝ) ≤ A*Real.log (B z) → m-(ι ⟨0,hN⟩).val ≤ H →
--         v∈relaxedGeometricFamily m n budget c → (∀ i,v (ι i)=B (p i)) →
--         Real.exp (Real.exp 1) ≤ S → B S ≤ (H:ℝ)^4 →
--         (∀ i,IsNormalPrime S (p i)) → (∀ i,3 ≤ p i) → StrictAnti p →
--         0 < F → F.totient=d*r.totient → r=∏ i,p i →
--         (largestPrimeFactor d:ℝ) ≤ S → SquarefreeAbove F S → SquarefreeAbove F.totient S →
--         (∀ q:ℕ,q.Prime → q∣F → IsNormalPrime S q) →
--         largestPrimeFactor F≠p ⟨0,hN⟩ → (∀ i,(p i-1:ℕ) ≤ z) → (F.totient:ℝ) ≤ z →
--         z^(9/10:ℝ) ≤ p ⟨0,hN⟩ → Nonempty (PPTResidualGridWitness d N H z S A r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TotientAsymptotic.IsNormalPrime`, `OAI.TotientAsymptotic.PPTResidualGridWitness`, `OAI.TotientAsymptotic.SquarefreeAbove` and `OAI.TotientAsymptotic.relaxedGeometricFamily` (definitions bundle `OAIQ233A000` of this split); `OAI.TotientAsymptotic.B` and `OAI.TotientAsymptotic.largestPrimeFactor` (the published bundle `Def_TotientAsymptotic`).
--
--   **Used by.** The proof of `OAI.TotientAsymptotic.ppt_regular_geometric_count` of this split imports it.
-- source:
--   OpenAI, An asymptotic formula for the number of totients (result family 024), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 24; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-asymptotic-formula-for-the-number-of-totients-September-25-2026/An-asymptotic-formula-for-the-number-of-totients-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/PPTRegularWitness.lean (declaration OAI.TotientAsymptotic.ppt_regular_geometric_witness)

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Antidiag.Nat
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
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Squarefree
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
import Mathlib.NumberTheory.SelbergSieve
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
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

theorem ppt_regular_geometric_witness (d : ℕ) (hd : 0 < d) {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop,
    ∀ (m n N H F r : ℕ) (p : Fin N → ℕ) (v : Fin n → ℝ)
      (ι : Fin N ↪o Fin n) (budget c S : ℝ),∀ hN : 0 < N,
      n ≤ m → N ≤ H → (H:ℝ) ≤ A*Real.log (B z) → m-(ι ⟨0,hN⟩).val ≤ H →
      v∈relaxedGeometricFamily m n budget c → (∀ i,v (ι i)=B (p i)) →
      Real.exp (Real.exp 1) ≤ S → B S ≤ (H:ℝ)^4 →
      (∀ i,IsNormalPrime S (p i)) → (∀ i,3 ≤ p i) → StrictAnti p →
      0 < F → F.totient=d*r.totient → r=∏ i,p i →
      (largestPrimeFactor d:ℝ) ≤ S → SquarefreeAbove F S → SquarefreeAbove F.totient S →
      (∀ q:ℕ,q.Prime → q∣F → IsNormalPrime S q) →
      largestPrimeFactor F≠p ⟨0,hN⟩ → (∀ i,(p i-1:ℕ) ≤ z) → (F.totient:ℝ) ≤ z →
      z^(9/10:ℝ) ≤ p ⟨0,hN⟩ → Nonempty (PPTResidualGridWitness d N H z S A r) := by
  sorry

end TotientAsymptotic

end

end OAI
end
