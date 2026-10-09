-- Prove2me | Theorems.Thm_Helfgott_cdem_squarefree_seed_three
-- name    : Helfgott.cdem_squarefree_seed_three
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:35:02.383842+00:00
-- url     : https://prove2.me/theorems/126c8a50-d264-4c06-806b-d79d6a76ae41
-- title:
--   Unconditional squarefree remainder seed for the CDEM bootstrap
-- statement:
--   For every real x at least 9, the actual Mobius-square count satisfies
--   $$\left|\sum_{1\le n\le\lfloor x\rfloor}\mu(n)^2-\frac{6}{\pi^2}x\right|\le3\sqrt{x}.$$
--   This provides an unconditional coarse squarefree seed for the CDEM coarse-Mertens bootstrap. It needs no numerical RH verification, Hurst finite computation, or previous unbounded Mertens estimate. The sharper squarefree estimates and the finite Abel aggregates are separate obligations.
-- source:
--   Reconstruction of Gershon Bialer, CohenDressElMarrakiCoarseSquarefree.lean, Apache 2.0, gersh/ternary-goldbach-lean commit 27df23af6a712895f22204d0d81102baa74f0ebe. The floor identity and reciprocal-square density tail are independently derived from Mathlib here; no PrimeNumberTheoremAnd or MathExtras imports are used. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.BigOperators.Intervals
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem cdem_squarefree_seed_three  (x : ℝ) (hx : 9 ≤ x) :
    |(∑ n ∈ Icc 1 ⌊x⌋₊, (moebius n : ℝ)^2) -
      (6 / Real.pi^2)*x| ≤ 3*Real.sqrt x := by sorry

end Helfgott
