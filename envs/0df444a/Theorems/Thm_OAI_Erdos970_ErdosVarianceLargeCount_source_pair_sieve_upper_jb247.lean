-- Prove2me | Theorems.Thm_OAI_Erdos970_ErdosVarianceLargeCount_source_pair_sieve_upper_jb247
-- name    : OAI.Erdos970.ErdosVarianceLargeCount.source_pair_sieve_upper_jb247
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:47:47.315929+00:00
-- url     : https://prove2.me/theorems/aa45eefe-8e10-4b03-9389-ae7f275b580e
-- title:
--   OAI.Erdos970.ErdosVarianceLargeCount.source_pair_sieve_upper_jb247: intermediate lemma from OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Erdos970.ErdosVarianceLargeCount.source_pair_sieve_upper` of [lean/OAI/NumberTheory/Jacobsthal/Sieve/SourcePairSieve.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Sieve/SourcePairSieve.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Erdos970.ErdosVarianceLargeCount`, with `open NumberTheoryLean ErdosHyperbolaError`):
--
--   ```lean
--   theorem source_pair_sieve_upper_jb247 (H T0 T1 : ℕ) (hH : 2 ≤ H) (hT0 : 0 < T0) (hT1 : 0 < T1)
--       (hSF : Squarefree T0) (hsupport : ∀ t : ℕ,t.Prime → t ∣ T0 → t ∣ H)
--       (hT1N : T1.Coprime (H*T0)) (C0 k0 p0 p1 m1 : ℤ)
--       (hC0 : Int.gcd C0 (H : ℤ) = 1) (hp0 : Int.gcd p0 (T0 : ℤ) = 1)
--       (hp1 : Int.gcd p1 (T1 : ℤ) = 1) (P : Finset ℕ) (hP : ∀ t ∈ P,t.Prime)
--       (hPcop : ∀ t ∈ P,t.Coprime (H*T1)) (v s : ℝ) (hv : 2 ≤ v) (hs : 480024 ≤ s)
--       (hPv : ∀ t ∈ P,(t : ℝ) ≤ v)
--       (x0 x1 y0 y1 : ℝ) (hx : x0 ≤ x1) (hy : y0 ≤ y1) (lcI rcI lcJ rcJ : Bool) :
--       ((siftedSourcePairs H T0 T1 C0 k0 p0 p1 m1 x0 x1 y0 y1 lcI rcI lcJ rcJ P).card : ℝ) ≤
--         sourceMain H T0 T1 (x1-x0) (y1-y0)*(∏ t ∈ P,(1-1/(t : ℝ)))*(1+Real.exp (-s/96))+
--         ∑ d ∈ RealFundamentalSieve.levelDivisors P v s,
--           hyperbolaEnvelope H T0*(1+(x1-x0)/((d : ℝ)*((H*T0 : ℕ) : ℝ))+(y1-y0)/((H*T0 : ℕ) : ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Erdos970.ErdosVarianceLargeCount.hyperbolaEnvelope`, `OAI.Erdos970.ErdosVarianceLargeCount.siftedSourcePairs` and `OAI.Erdos970.ErdosVarianceLargeCount.sourceMain` (definitions bundle `OAIQ247J003` of this split); `OAI.Erdos970.NumberTheoryLean.RealFundamentalSieve.levelDivisors` (definitions bundle `OAIQ247J004` of this split).
--
--   **Used by.** The proofs of `OAI.Erdos970.ErdosVarianceLargeMap.source_full_pattern_domination_jb247` and `OAI_Erdos970_ErdosVarianceLargeScale_source_large_pair_bound_jb247` of this split import it.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Jacobsthal/Sieve/SourcePairSieve.lean (declaration OAI.Erdos970.ErdosVarianceLargeCount.source_pair_sieve_upper)

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_OAIQ247J003
import Definitions.Def_OAIQ247J004

section

attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

namespace ErdosVarianceLargeCount
open NumberTheoryLean ErdosHyperbolaError
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_pair_sieve_upper_jb247 (H T0 T1 : ℕ) (hH : 2 ≤ H) (hT0 : 0 < T0) (hT1 : 0 < T1)
    (hSF : Squarefree T0) (hsupport : ∀ t : ℕ,t.Prime → t ∣ T0 → t ∣ H)
    (hT1N : T1.Coprime (H*T0)) (C0 k0 p0 p1 m1 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (hp0 : Int.gcd p0 (T0 : ℤ) = 1)
    (hp1 : Int.gcd p1 (T1 : ℤ) = 1) (P : Finset ℕ) (hP : ∀ t ∈ P,t.Prime)
    (hPcop : ∀ t ∈ P,t.Coprime (H*T1)) (v s : ℝ) (hv : 2 ≤ v) (hs : 480024 ≤ s)
    (hPv : ∀ t ∈ P,(t : ℝ) ≤ v)
    (x0 x1 y0 y1 : ℝ) (hx : x0 ≤ x1) (hy : y0 ≤ y1) (lcI rcI lcJ rcJ : Bool) :
    ((siftedSourcePairs H T0 T1 C0 k0 p0 p1 m1 x0 x1 y0 y1 lcI rcI lcJ rcJ P).card : ℝ) ≤
      sourceMain H T0 T1 (x1-x0) (y1-y0)*(∏ t ∈ P,(1-1/(t : ℝ)))*(1+Real.exp (-s/96))+
      ∑ d ∈ RealFundamentalSieve.levelDivisors P v s,
        hyperbolaEnvelope H T0*(1+(x1-x0)/((d : ℝ)*((H*T0 : ℕ) : ℝ))+(y1-y0)/((H*T0 : ℕ) : ℝ)) := by
  sorry

end ErdosVarianceLargeCount

end Erdos970

end OAI
end
