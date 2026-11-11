-- Prove2me | Theorems.Thm_OAI_TotientAsymptotic_actual_positive_collision_count
-- name    : OAI.TotientAsymptotic.actual_positive_collision_count
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:31:56.859893+00:00
-- url     : https://prove2.me/theorems/dcaec9c6-4fd6-4ce5-a240-618701476971
-- title:
--   OAI.TotientAsymptotic.actual_positive_collision_count: intermediate lemma from OpenAI, An asymptotic formula for the number of totients (result family 024)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TotientAsymptotic.coefficient_nonnegative`, `OAI.TotientAsymptotic.totient_asymptotic_formula`, `OAI.TotientAsymptotic.weighted_totient_asymptotic` and `OAI.TotientAsymptotic.weighted_totient_one_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An asymptotic formula for the number of totients (result family 024)*, OpenAI Math Release, September 25, 2026, result family 24, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TotientAsymptotic.actual_positive_collision_count` of [lean/OAI/NumberTheory/TotientAsymptotic/RestoreCommonPrefix.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/RestoreCommonPrefix.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TotientAsymptotic`, with `open scoped BigOperators Topology`, `open Filter`):
--
--   ```lean
--   theorem actual_positive_collision_count (hford : FordLemma51Input) (hmertens : MertensProductInput)
--       (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) :
--       ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
--       ∀ i : ℕ, 1 ≤ i → i ≤ R x H → ∀ t ≤ x,
--       ((firstCollisionPairs x H t i).card : ℝ) ≤
--         (160/Real.log 2)*(x/Real.log x)*G x (m x)*((m x-i : ℕ) : ℝ)^4*
--           Real.exp (-fordBandScale x i/(16*((m x-i : ℕ) : ℝ)^4))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TotientAsymptotic.FordLemma51Input`, `OAI.TotientAsymptotic.FordRenewalInput`, `OAI.TotientAsymptotic.FordUnitPrimeBoxInput`, `OAI.TotientAsymptotic.MertensProductInput`, `OAI.TotientAsymptotic.R`, `OAI.TotientAsymptotic.TotientTuple`, `OAI.TotientAsymptotic.firstCollisionPairs` and `OAI.TotientAsymptotic.fordBandScale` (definitions bundle `OAIQ233A000` of this split); `OAI.TotientAsymptotic.G` and `OAI.TotientAsymptotic.m` (the published bundle `Def_TotientAsymptotic`).
--
--   **Used by.** The proofs of `OAI.TotientAsymptotic.companion_one_two_without_seed_input_of_structure`, `OAI.TotientAsymptotic.conditional_companion_additive`, `OAI.TotientAsymptotic.conditional_companion_theorem_of_structure` and `OAI.TotientAsymptotic.conditional_main_theorem_of_structure` of this split import it.
-- source:
--   OpenAI, An asymptotic formula for the number of totients (result family 024), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 24; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-asymptotic-formula-for-the-number-of-totients-September-25-2026/An-asymptotic-formula-for-the-number-of-totients-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/RestoreCommonPrefix.lean (declaration OAI.TotientAsymptotic.actual_positive_collision_count)

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

theorem actual_positive_collision_count (hford : FordLemma51Input) (hmertens : MertensProductInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, 1 ≤ i → i ≤ R x H → ∀ t ≤ x,
    ((firstCollisionPairs x H t i).card : ℝ) ≤
      (160/Real.log 2)*(x/Real.log x)*G x (m x)*((m x-i : ℕ) : ℝ)^4*
        Real.exp (-fordBandScale x i/(16*((m x-i : ℕ) : ℝ)^4)) := by
  sorry

end TotientAsymptotic

end

end OAI
end
