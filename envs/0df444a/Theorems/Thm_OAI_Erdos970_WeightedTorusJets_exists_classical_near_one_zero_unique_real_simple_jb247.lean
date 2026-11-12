-- Prove2me | Theorems.Thm_OAI_Erdos970_WeightedTorusJets_exists_classical_near_one_zero_unique_real_simple_jb247
-- name    : OAI.Erdos970.WeightedTorusJets.exists_classical_near_one_zero_unique_real_simple_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:40:11.205861+00:00
-- url     : https://prove2.me/theorems/3781ab84-9ce1-4a1d-9abe-04e141b1f303
-- title:
--   OAI.Erdos970.WeightedTorusJets.exists_classical_near_one_zero_unique_real_simple_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.WeightedTorusJets.exists_classical_near_one_zero_unique_real_simple` of [lean/OAI/NumberTheory/Jacobsthal/Siegel/NormLogDerivLFunctionNegLogDerivZeta.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Siegel/NormLogDerivLFunctionNegLogDerivZeta.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.WeightedTorusJets`, with `open DirichletCharacter`, `open scoped ComplexConjugate`):
--
--   ```lean
--   theorem exists_classical_near_one_zero_unique_real_simple_jb247 :
--       ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) (hq : 3 ≤ q),
--         let _ : NeZero q := ⟨by omega⟩
--         ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
--         (∀ a : ZMod q, (χ a).im = 0) → ∀ z : ℂ,
--         ‖z - 1‖ ≤ c / Real.log q → LFunction χ z = 0 →
--         z.im = 0 ∧ analyticOrderAt (LFunction χ) z = 1 ∧
--           ∀ w : ℂ, ‖w - 1‖ ≤ c / Real.log q → LFunction χ w = 0 → w = z
--   ```
--
--   **Used by.** The proofs of `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_primitive_real_zero_free_disk_jb247` and `OAI_Erdos970_Erdos970Dependency_SiegelWalfisz_exists_primitive_zero_free_region_jb247` of this split import it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Siegel/NormLogDerivLFunctionNegLogDerivZeta.lean (declaration OAI.Erdos970.WeightedTorusJets.exists_classical_near_one_zero_unique_real_simple)

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

namespace WeightedTorusJets

open DirichletCharacter
open scoped ComplexConjugate

theorem exists_classical_near_one_zero_unique_real_simple_jb247 :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) (hq : 3 ≤ q),
      let _ : NeZero q := ⟨by omega⟩
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      (∀ a : ZMod q, (χ a).im = 0) → ∀ z : ℂ,
      ‖z - 1‖ ≤ c / Real.log q → LFunction χ z = 0 →
      z.im = 0 ∧ analyticOrderAt (LFunction χ) z = 1 ∧
        ∀ w : ℂ, ‖w - 1‖ ≤ c / Real.log q → LFunction χ w = 0 → w = z := by
  sorry

end WeightedTorusJets

end

end Erdos970

end OAI
end
