-- Prove2me | Theorems.Thm_OAI_Erdos970_WeightedTorusJets_source_biquadratic_arithmetic_of_field_ne_jb247
-- name    : OAI.Erdos970.WeightedTorusJets.source_biquadratic_arithmetic_of_field_ne_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:50:54.821388+00:00
-- url     : https://prove2.me/theorems/1bb1241e-a9f4-4713-a3de-15f09beb4f99
-- title:
--   OAI.Erdos970.WeightedTorusJets.source_biquadratic_arithmetic_of_field_ne_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.WeightedTorusJets.source_biquadratic_arithmetic_of_field_ne` of [lean/OAI/NumberTheory/Jacobsthal/Siegel/SqrtTwoField.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Siegel/SqrtTwoField.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.WeightedTorusJets`, with `open scoped _root_.Erdos970`, `open scoped Pointwise`, `open scoped NumberField`, `open scoped NumberField`, `open scoped NumberField`, `open NumberField`):
--
--   ```lean
--   theorem source_biquadratic_arithmetic_of_field_ne_jb247 (q : ℕ) [NeZero q]
--       (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L]
--       [NeZero (8 * q)] [IsAbelianGalois ℚ L]
--       (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
--       (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (hfield : characterField (8 * q) L ℂ
--         (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠ sourceSqrtTwoField q L) :
--       ∃ (d : ℤ) (a b : L), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
--         ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : L) ∧ b ^ 2 = 2 ∧
--         IntermediateField.adjoin ℚ {a} = characterField (8 * q) L ℂ
--           (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
--         (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
--         Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
--         NumberField.discr (IntermediateField.adjoin ℚ {a}) =
--           (if d % 4 = 1 then d else 4 * d) ∧
--         let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
--         let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
--         let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
--         ∃ v : Module.Basis (Fin 4) ℚ B,
--           (∀ i, v i = ![1, a', b', a' * b'] i) ∧
--           (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
--           ∃ σ τ : B ≃ₐ[ℚ] B,
--             σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
--             Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
--             (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
--             (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
--             ∀ (p : ℕ), p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
--               ((∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - σ • x) ∨
--                 (∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - (σ * τ) • x))
--   ```
--
--   **Definitions.** The statement is written with `Int.IsFundamentalDiscr` (definitions bundle `OAIQ247J001` of this split); `OAI.Erdos970.WeightedTorusJets.characterField` and `OAI.Erdos970.WeightedTorusJets.sourceSqrtTwoField` (definitions bundle `OAIQ247J005` of this split).
--
--   **Used by.** The proofs of `OAI_Erdos970_WeightedTorusJets_source_character_global_greedy_determinant_divisibility_jb247` and `OAI.Erdos970.WeightedTorusJets.source_character_global_greedy_determinant_local_bounds_jb247` of this split import it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Siegel/SqrtTwoField.lean (declaration OAI.Erdos970.WeightedTorusJets.source_biquadratic_arithmetic_of_field_ne)

import Mathlib
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_OAIQ247J001
import Definitions.Def_OAIQ247J005

section

attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField

namespace WeightedTorusJets

open NumberField

theorem source_biquadratic_arithmetic_of_field_ne_jb247 (q : ℕ) [NeZero q]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L]
    [NeZero (8 * q)] [IsAbelianGalois ℚ L]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (hfield : characterField (8 * q) L ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠ sourceSqrtTwoField q L) :
    ∃ (d : ℤ) (a b : L), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : L) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) L ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ (p : ℕ), p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
            ((∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - σ • x) ∨
              (∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - (σ * τ) • x)) := by
  sorry

end WeightedTorusJets

end

end Erdos970

end OAI
end
