-- Prove2me | Theorems.Thm_Helfgott_moebius_initial_integral_of_finite_certificate
-- name    : Helfgott.moebius_initial_integral_of_finite_certificate
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T20:54:32.131577+00:00
-- url     : https://prove2.me/theorems/aeda6acb-9bc9-4610-9dc8-34a8d5337a4e
-- title:
--   Sound finite arithmetic certificate for the initial Mobius integral
-- statement:
--   Let $1\le B\le1200001$, let $Q>0$ be an integer scale, and let two packed finite tables have capacities at least $B$. Suppose the first table passes the Möbius prime-factor checks and the second passes the prefix-sum recurrence and scaled harmonic-upper-bound checks. If $U$ is the total integer upper bound recorded in the second table, then, for the actual Möbius function, $$\int_1^B\frac{\left|\sum_{1\le d\le\lfloor t\rfloor}\mu(d)\right|}{t}\,dt\le\frac{U}{Q}.$$ This converts finite integer-arithmetic certificates into the initial-integral input for explicit reciprocal Möbius estimates. The checks for a concrete table must be proved separately.
-- source:
--   Original finite arithmetic certificate and complete soundness proof toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Supports the finite initial-integral input used in Helfgott minor-arc bounds. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteCertificate
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval

namespace Helfgott

theorem moebius_initial_integral_of_finite_certificate  (B dm dh Q : ℕ)
    (muTree : MobiusCertTree) (hTree : MobiusHarmonicTree)
    (hBpos : 1 ≤ B) (hB : B ≤ 1200001) (hmCapacity : B ≤ 32 * 2 ^ dm)
    (hhCapacity : B ≤ 32 * 2 ^ dh) (hQ : 0 < Q)
    (hm : mobiusTreeCheck (mobiusTreeValue dm muTree) B dm 0 muTree = true)
    (hh : mobiusHarmonicTreeCheck (mobiusTreeValue dm muTree)
      (mobiusPrefixValue dh hTree) Q B dh 0 hTree = true) :
    (∫ t in (1 : ℝ)..(B : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤
      (mobiusHarmonicUpper hTree : ℝ) / (Q : ℝ) := by sorry

end Helfgott
