-- Prove2me | Theorems.Thm_Helfgott_cdem_prefix_199330
-- name    : Helfgott.cdem_prefix_199330
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T03:09:31.362254+00:00
-- url     : https://prove2.me/theorems/e4de72e7-3bf5-49a6-8517-9d13b11cda0f
-- title:
--   Exact actual-Mobius CDEM prefix and endpoint certificate at K=199330
-- statement:
--   At K=199330 the actual Mobius function has summatory value -6 and absolute mass 121174. Its weighted floor sum at N=5,000,000,000 is exactly 112. The reciprocal prefix sum is enclosed between 20985957655978471021715/10^30 and 20985957655978471142885/10^30. The floor sum minus one is exactly 111, and 1/sqrt(5,000,000,001) is at most 14142135622317/10^18. These are unconditional exact prefix and endpoint inputs for the reproducible CDEM coarse-Mertens bootstrap. The large Abel aggregate computations and the unbounded Mertens conclusion are separate obligations.
-- source:
--   Independent kernel-checked reconstruction of the CDEM prefix constants in gersh/ternary-goldbach-lean, pinned commit 27df23af6a712895f22204d0d81102baa74f0ebe, CohenDressElMarrakiReproducibleSourceDefs.lean. The proof reuses accepted Mobius-value certificates and exact integer aggregate blocks, with rigorous reciprocal rounding. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem cdem_prefix_199330 :
    (∑ n ∈ Icc 1 199330, moebius n) = (-6 : ℤ) ∧
    (∑ n ∈ Icc 1 199330, (moebius n).natAbs) = 121174 ∧
    (∑ n ∈ Icc 1 199330, moebius n * (5000000000 / n : ℕ)) = (112 : ℤ) ∧
    (20985957655978471021715 / 1000000000000000000000000000000 : ℝ) ≤
      (∑ n ∈ Icc 1 199330, ((moebius n : ℤ) : ℝ) / (n : ℝ)) ∧
    (∑ n ∈ Icc 1 199330, ((moebius n : ℤ) : ℝ) / (n : ℝ)) ≤
      (20985957655978471142885 / 1000000000000000000000000000000 : ℝ) ∧
    ((∑ n ∈ Icc 1 199330, moebius n * (5000000000 / n : ℕ)) - 1 : ℤ) = 111 ∧
    1 / Real.sqrt (5000000001 : ℝ) ≤
      (14142135622317 / 1000000000000000000 : ℝ) := by sorry

end Helfgott
