-- Prove2me | Theorems.Thm_OAI_TotientAsymptotic_actual_block_count
-- name    : OAI.TotientAsymptotic.actual_block_count
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:31:23.016612+00:00
-- url     : https://prove2.me/theorems/55898209-fbef-4618-824f-1408cb546aa4
-- title:
--   OAI.TotientAsymptotic.actual_block_count: intermediate lemma from OpenAI, An asymptotic formula for the number of totients (result family 024)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TotientAsymptotic.coefficient_nonnegative`, `OAI.TotientAsymptotic.totient_asymptotic_formula`, `OAI.TotientAsymptotic.weighted_totient_asymptotic` and `OAI.TotientAsymptotic.weighted_totient_one_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An asymptotic formula for the number of totients (result family 024)*, OpenAI Math Release, September 25, 2026, result family 24, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TotientAsymptotic.actual_block_count` of [lean/OAI/NumberTheory/TotientAsymptotic/ActualBlockCount.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/ActualBlockCount.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TotientAsymptotic`, with `open scoped BigOperators Topology`, `open Filter`):
--
--   ```lean
--   theorem actual_block_count (hford : FordLemma51Input) (hmertens : MertensProductInput) :
--       ∃ y₀ : ℝ, 1 < y₀ ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
--       ∀ i : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → ∀ t y : ℝ,
--       y₀ ≤ y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y → B y ≤ 2*fordBandScale x i →
--       ∀ (Q : Finset (TotientTuple (R x H) × TotientTuple (R x H))),
--       (∀ q ∈ Q, GoodCollisionBlock x t H i y q) →
--       Set.InjOn (fun q : TotientTuple (R x H) × TotientTuple (R x H) => pairSuffix q i) (↑Q : Set _) →
--       (Q.card : ℝ) ≤ y/Real.log y*Real.exp (-B y/(8*((m x-i : ℕ) : ℝ)^4))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TotientAsymptotic.FordLemma51Input`, `OAI.TotientAsymptotic.GoodCollisionBlock`, `OAI.TotientAsymptotic.L`, `OAI.TotientAsymptotic.MertensProductInput`, `OAI.TotientAsymptotic.PrefixDatum`, `OAI.TotientAsymptotic.R`, `OAI.TotientAsymptotic.TotientTuple`, `OAI.TotientAsymptotic.fordBandScale` and `OAI.TotientAsymptotic.pairSuffix` (definitions bundle `OAIQ233A000` of this split); `OAI.TotientAsymptotic.B` and `OAI.TotientAsymptotic.m` (the published bundle `Def_TotientAsymptotic`).
--
--   **Used by.** The proofs of `OAI.TotientAsymptotic.actual_positive_collision_count`, `OAI.TotientAsymptotic.companion_one_two_without_seed_input_of_structure`, `OAI.TotientAsymptotic.conditional_companion_additive`, `OAI.TotientAsymptotic.conditional_companion_theorem_of_structure` and `OAI.TotientAsymptotic.conditional_main_theorem_of_structure` of this split import it.
-- source:
--   OpenAI, An asymptotic formula for the number of totients (result family 024), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 24; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-asymptotic-formula-for-the-number-of-totients-September-25-2026/An-asymptotic-formula-for-the-number-of-totients-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/ActualBlockCount.lean (declaration OAI.TotientAsymptotic.actual_block_count)

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

theorem actual_block_count (hford : FordLemma51Input) (hmertens : MertensProductInput) :
    ∃ y₀ : ℝ, 1 < y₀ ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → ∀ t y : ℝ,
    y₀ ≤ y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y → B y ≤ 2*fordBandScale x i →
    ∀ (Q : Finset (TotientTuple (R x H) × TotientTuple (R x H))),
    (∀ q ∈ Q, GoodCollisionBlock x t H i y q) →
    Set.InjOn (fun q : TotientTuple (R x H) × TotientTuple (R x H) => pairSuffix q i) (↑Q : Set _) →
    (Q.card : ℝ) ≤ y/Real.log y*Real.exp (-B y/(8*((m x-i : ℕ) : ℝ)^4)) := by
  sorry

end TotientAsymptotic

end

end OAI
end
