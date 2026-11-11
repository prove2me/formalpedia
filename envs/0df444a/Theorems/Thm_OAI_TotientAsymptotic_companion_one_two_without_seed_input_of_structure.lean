-- Prove2me | Theorems.Thm_OAI_TotientAsymptotic_companion_one_two_without_seed_input_of_structure
-- name    : OAI.TotientAsymptotic.companion_one_two_without_seed_input_of_structure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:32:27.400685+00:00
-- url     : https://prove2.me/theorems/ace868b3-d338-48af-8e4a-4d44bc8eed0a
-- title:
--   OAI.TotientAsymptotic.companion_one_two_without_seed_input_of_structure: intermediate lemma from OpenAI, An asymptotic formula for the number of totients (result family 024)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TotientAsymptotic.coefficient_nonnegative`, `OAI.TotientAsymptotic.totient_asymptotic_formula`, `OAI.TotientAsymptotic.weighted_totient_asymptotic` and `OAI.TotientAsymptotic.weighted_totient_one_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An asymptotic formula for the number of totients (result family 024)*, OpenAI Math Release, September 25, 2026, result family 24, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TotientAsymptotic.companion_one_two_without_seed_input_of_structure` of [lean/OAI/NumberTheory/TotientAsymptotic/SeedConsequences.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/SeedConsequences.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TotientAsymptotic`, with `open scoped Topology`):
--
--   ```lean
--   theorem companion_one_two_without_seed_input_of_structure (hscale : FordScaleBounds)
--       (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
--       (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
--       (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput)
--       (hppt : ∀ d : ℕ, IsTotient d → PPTBoundedFiberPropagation d) :
--       ∀ k∈({1,2} : Finset ℕ), ∃ c : ℝ, 0 < c ∧
--         ∀ s∈Set.Ico (0 : ℝ) 1, c≤A (fk k) s
--   ```
--
--   **Definitions.** The statement is written with `OAI.TotientAsymptotic.ExtractedStructureInput`, `OAI.TotientAsymptotic.FordCoordinateConcentrationInput`, `OAI.TotientAsymptotic.FordLemma26Input`, `OAI.TotientAsymptotic.FordLemma51Input`, `OAI.TotientAsymptotic.FordRenewalInput`, `OAI.TotientAsymptotic.FordScaleBounds`, `OAI.TotientAsymptotic.FordUnitPrimeBoxInput`, `OAI.TotientAsymptotic.MertensProductInput`, `OAI.TotientAsymptotic.PPTBoundedFiberPropagation` and `OAI.TotientAsymptotic.PrimeNumberTheoremInput` (definitions bundle `OAIQ233A000` of this split); `OAI.TotientAsymptotic.A`, `OAI.TotientAsymptotic.IsTotient` and `OAI.TotientAsymptotic.fk` (the published bundle `Def_TotientAsymptotic`).
--
--   **Used by.** The proof of `OAI.TotientAsymptotic.weighted_totient_one_two` of this split imports it.
-- source:
--   OpenAI, An asymptotic formula for the number of totients (result family 024), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 24; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-asymptotic-formula-for-the-number-of-totients-September-25-2026/An-asymptotic-formula-for-the-number-of-totients-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/SeedConsequences.lean (declaration OAI.TotientAsymptotic.companion_one_two_without_seed_input_of_structure)

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
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.Divisors
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
open scoped Topology
namespace TotientAsymptotic

theorem companion_one_two_without_seed_input_of_structure (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput)
    (hppt : ∀ d : ℕ, IsTotient d → PPTBoundedFiberPropagation d) :
    ∀ k∈({1,2} : Finset ℕ), ∃ c : ℝ, 0 < c ∧
      ∀ s∈Set.Ico (0 : ℝ) 1, c≤A (fk k) s := by
  sorry

end TotientAsymptotic

end

end OAI
end
