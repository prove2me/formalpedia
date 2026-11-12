-- Prove2me | Theorems.Thm_OAI_Erdos970_WeightedTorusJets_source_given_determinant_finite_lower_of_real_zero_jb247
-- name    : OAI.Erdos970.WeightedTorusJets.source_given_determinant_finite_lower_of_real_zero_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:40:05.079426+00:00
-- url     : https://prove2.me/theorems/8388f4cc-22cc-47cb-8a86-5f56589aa888
-- title:
--   OAI.Erdos970.WeightedTorusJets.source_given_determinant_finite_lower_of_real_zero_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.WeightedTorusJets.source_given_determinant_finite_lower_of_real_zero` of [lean/OAI/NumberTheory/Jacobsthal/Siegel/NormSqReal.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Siegel/NormSqReal.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.WeightedTorusJets`, with `open scoped BigOperators`, `open scoped Pointwise`, `open scoped NumberField`, `open scoped NumberField`, `open scoped NumberField`, `open scoped NumberField`, `open scoped BigOperators`, `open scoped BigOperators`, `open Module`, `open scoped BigOperators`, `open scoped BigOperators`, `open Module`, `open scoped BigOperators`, `open InnerProductSpace`, `open scoped BigOperators NumberField`, `open scoped BigOperators NumberField`):
--
--   ```lean
--   theorem source_given_determinant_finite_lower_of_real_zero_jb247 :
--       ∃ C : ℝ, 0 < C ∧ Real.log 4 ≤ C ∧
--         ∀ H : ℕ, ∃ CH : ℝ,
--           ∀ (q : ℕ) [NeZero q], ∀ χ : DirichletCharacter ℂ q,
--             χ.IsPrimitive → χ ≠ 1 → (∀ x : ZMod q, (χ x).im = 0) →
--           ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
--           ∀ (K : Type*) [Field K] [NumberField K], Module.finrank ℚ K = 4 →
--           ∀ (m : ℕ) (Δ : 𝓞 K), Δ ≠ 0 → ∀ α : Fin m → Fin 3 → ℕ,
--             (∀ p : ℕ, p.Prime → H < p → ¬p ∣ 2 * q → χ (p : ZMod q) = -1 →
--               Δ ∈ (Ideal.span {(p : 𝓞 K)}) ^ (∑ i, α i 0 / p)) →
--           ∀ U : ℝ, 0 ≤ U →
--             (∑ i, (α i 0 : ℝ)) *
--                 (Real.log U - C * Real.log q -
--                   C * ((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q - CH) -
--               C * m * U ≤ (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)|
--   ```
--
--   **Used by.** The proofs of `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_primitive_real_zero_free_disk_jb247`, `OAI_Erdos970_WeightedTorusJets_dirichletRealZeroBound_proof_jb247` and `OAI_Erdos970_WeightedTorusJets_source_character_global_greedy_determinant_full_local_bounds_jb247` of this split import it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Siegel/NormSqReal.lean (declaration OAI.Erdos970.WeightedTorusJets.source_given_determinant_finite_lower_of_real_zero)

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

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section
open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators
open scoped BigOperators
open Module
open scoped BigOperators
open scoped BigOperators
open Module
open scoped BigOperators
open InnerProductSpace

open scoped BigOperators NumberField

namespace WeightedTorusJets

open scoped BigOperators NumberField

theorem source_given_determinant_finite_lower_of_real_zero_jb247 :
    ∃ C : ℝ, 0 < C ∧ Real.log 4 ≤ C ∧
      ∀ H : ℕ, ∃ CH : ℝ,
        ∀ (q : ℕ) [NeZero q], ∀ χ : DirichletCharacter ℂ q,
          χ.IsPrimitive → χ ≠ 1 → (∀ x : ZMod q, (χ x).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
        ∀ (K : Type*) [Field K] [NumberField K], Module.finrank ℚ K = 4 →
        ∀ (m : ℕ) (Δ : 𝓞 K), Δ ≠ 0 → ∀ α : Fin m → Fin 3 → ℕ,
          (∀ p : ℕ, p.Prime → H < p → ¬p ∣ 2 * q → χ (p : ZMod q) = -1 →
            Δ ∈ (Ideal.span {(p : 𝓞 K)}) ^ (∑ i, α i 0 / p)) →
        ∀ U : ℝ, 0 ≤ U →
          (∑ i, (α i 0 : ℝ)) *
              (Real.log U - C * Real.log q -
                C * ((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q - CH) -
            C * m * U ≤ (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)| := by
  sorry

end WeightedTorusJets

end

end Erdos970

end OAI
end
