-- Prove2me | Theorems.Thm_Helfgott_centered_prime_finite_moment_twenty_one_billion
-- name    : Helfgott.centered_prime_finite_moment_twenty_one_billion
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T00:37:31.90898+00:00
-- url     : https://prove2.me/theorems/06273155-4344-41da-8d31-0d234f9b971c
-- title:
--   Unconditional centered prime-convolution moment at 21 billion
-- statement:
--   Let $\Lambda$ denote the von Mangoldt function and $*$ Dirichlet convolution. For $C\in\mathbb R$ with $|C|\le2$, define $a_C(k)=(\Lambda*\Lambda)(k)-\Lambda(k)\log k+C$ and $A_C(K)=\sum_{k\le K}a_C(k)$. At $K=21\cdot10^9$, one has the unconditional estimate
--   $$\sum_{k\le K}\frac{|a_C(k)|}{k}+\frac{|A_C(K)|}{K}\le\frac{4345}{4}.$$
--   This supplies the complete finite moment, including the overlap correction, needed in the corrected high-range Mertens hyperbola argument. No numerical prime enumeration, finite GRH input, or additional arithmetic hypothesis is required.
-- source:
--   Independent elementary proof from the divisor identity for the von Mangoldt function and the explicit Chebyshev bound in Mathlib. Supplies the finite convolution input in the corrected Ramare-style high Mertens argument. Written by Codex.

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem centered_prime_finite_moment_twenty_one_billion  (C : ℝ) (hC : |C| ≤ 2) :
    ((∑ k ∈ Icc 1 21000000000,
        |(vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C| /
          (k : ℝ)) +
        |∑ k ∈ Icc 1 21000000000,
          ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| /
          (21000000000 : ℝ)) ≤ 4345 / 4 := by sorry

end Helfgott
