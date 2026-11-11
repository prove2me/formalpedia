-- Prove2me | Theorems.Thm_OAI_TotientAsymptotic_actual_collision_exponent
-- name    : OAI.TotientAsymptotic.actual_collision_exponent
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:31:46.661417+00:00
-- url     : https://prove2.me/theorems/7b77f705-78f4-4a6e-8edc-c2d99157486f
-- title:
--   OAI.TotientAsymptotic.actual_collision_exponent: intermediate lemma from OpenAI, An asymptotic formula for the number of totients (result family 024)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TotientAsymptotic.coefficient_nonnegative`, `OAI.TotientAsymptotic.totient_asymptotic_formula`, `OAI.TotientAsymptotic.weighted_totient_asymptotic` and `OAI.TotientAsymptotic.weighted_totient_one_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An asymptotic formula for the number of totients (result family 024)*, OpenAI Math Release, September 25, 2026, result family 24, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TotientAsymptotic.actual_collision_exponent` of [lean/OAI/NumberTheory/TotientAsymptotic/ActualCollisionExponent.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/ActualCollisionExponent.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TotientAsymptotic`, with `open scoped BigOperators Topology`, `open Filter`):
--
--   ```lean
--   theorem actual_collision_exponent : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
--       ∀ i p q : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → p.Prime →
--       ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η → IsBasicRemainder x H ξ →
--       GoodWitnessConditions p η → GoodWitnessConditions q ξ →
--       tupleValue (witnessTuple p η)=tupleValue (witnessTuple q ξ) →
--       wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i →
--       (∀ j < i, wholeWitnessPrime p η j=wholeWitnessPrime q ξ j) → ∀ y : ℝ,
--       1 < y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y → B y ≤ 2*fordBandScale x i →
--       y^(9/10 : ℝ) ≤ wholeWitnessPrime p η i → y^(9/10 : ℝ) ≤ wholeWitnessPrime q ξ i →
--       (witnessBlockValue p η i (collisionLastIndex x i) : ℝ) ≤ y → (i=0 → y=x) →
--       let t := survivingPair p q η ξ i (collisionLastIndex x i)
--       let b := (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card
--       let Z := fordBandScale x (collisionLastIndex x i)
--       let δ := collisionMesh x y i
--       let Y := comparisonCutoffs y (pairUpperCoordinates t y Z δ)
--       let U := comparisonCutoffs y (pairLowerCoordinates t y δ)
--       (-2+(∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B y))+
--         comparisonError b y (normalityScale x i) Y U ≤ -1-1/(2*((m x-i : ℕ) : ℝ)^4))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TotientAsymptotic.GoodWitnessConditions`, `OAI.TotientAsymptotic.IsBasicRemainder`, `OAI.TotientAsymptotic.L`, `OAI.TotientAsymptotic.R`, `OAI.TotientAsymptotic.RemainderDatum`, `OAI.TotientAsymptotic.ShiftedPair`, `OAI.TotientAsymptotic.collisionLastIndex`, `OAI.TotientAsymptotic.collisionMesh`, `OAI.TotientAsymptotic.collisionSurvivors`, `OAI.TotientAsymptotic.comparisonCutoffs`, `OAI.TotientAsymptotic.comparisonError`, `OAI.TotientAsymptotic.fordBandScale`, `OAI.TotientAsymptotic.normalityScale`, `OAI.TotientAsymptotic.pairLowerCoordinates`, `OAI.TotientAsymptotic.pairUpperCoordinates`, `OAI.TotientAsymptotic.survivingPair`, `OAI.TotientAsymptotic.tupleValue`, `OAI.TotientAsymptotic.wholeWitnessPrime`, `OAI.TotientAsymptotic.witnessBlockValue` and `OAI.TotientAsymptotic.witnessTuple` (definitions bundle `OAIQ233A000` of this split); `OAI.TotientAsymptotic.B`, `OAI.TotientAsymptotic.a` and `OAI.TotientAsymptotic.m` (the published bundle `Def_TotientAsymptotic`).
--
--   **Used by.** The proof of `OAI.TotientAsymptotic.actual_block_count` of this split imports it.
-- source:
--   OpenAI, An asymptotic formula for the number of totients (result family 024), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 24; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-asymptotic-formula-for-the-number-of-totients-September-25-2026/An-asymptotic-formula-for-the-number-of-totients-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/TotientAsymptotic/ActualCollisionExponent.lean (declaration OAI.TotientAsymptotic.actual_collision_exponent)

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

namespace TotientAsymptotic

theorem actual_collision_exponent : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i p q : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → p.Prime →
    ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η → IsBasicRemainder x H ξ →
    GoodWitnessConditions p η → GoodWitnessConditions q ξ →
    tupleValue (witnessTuple p η)=tupleValue (witnessTuple q ξ) →
    wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i →
    (∀ j < i, wholeWitnessPrime p η j=wholeWitnessPrime q ξ j) → ∀ y : ℝ,
    1 < y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y → B y ≤ 2*fordBandScale x i →
    y^(9/10 : ℝ) ≤ wholeWitnessPrime p η i → y^(9/10 : ℝ) ≤ wholeWitnessPrime q ξ i →
    (witnessBlockValue p η i (collisionLastIndex x i) : ℝ) ≤ y → (i=0 → y=x) →
    let t := survivingPair p q η ξ i (collisionLastIndex x i)
    let b := (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card
    let Z := fordBandScale x (collisionLastIndex x i)
    let δ := collisionMesh x y i
    let Y := comparisonCutoffs y (pairUpperCoordinates t y Z δ)
    let U := comparisonCutoffs y (pairLowerCoordinates t y δ)
    (-2+(∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B y))+
      comparisonError b y (normalityScale x i) Y U ≤ -1-1/(2*((m x-i : ℕ) : ℝ)^4)) := by
  sorry

end TotientAsymptotic

end

end OAI
end
