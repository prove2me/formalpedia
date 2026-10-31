-- Prove2me | Theorems.Thm_LL_Decomp1528b_abel_recip
-- name    : LL_Decomp1528b.abel_recip
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:08:13.650982+00:00
-- url     : https://prove2.me/theorems/766ef2a8-97af-4494-b853-ac2faa1894b3
-- title:
--   Abel summation for the sum of reciprocals of primes
-- statement:
--   For real $x,y$ with $2\le y\le x$, let $A(t)=\sum_{p\le t}\log p/p$ over primes $p$ up to $\lfloor t\rfloor$. Then $\sum_{\lfloor y\rfloor<p\le\lfloor x\rfloor}1/p = A(x)/\log x - A(y)/\log y + \int_y^x A(t)/(t\log^2 t)\,dt$, the sum being over primes.
-- source:
--   Rosser and Schoenfeld, Illinois J. Math. 6 (1962), Section 4, p. 74 style; Montgomery and Vaughan, Multiplicative Number Theory I, Thm 2.7(d) proof

import Mathlib

open Real Finset Filter Topology

namespace LL_Decomp1528b
theorem abel_recip {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    ∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p =
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p) / log x -
        (∑ p ∈ Nat.primesLE ⌊y⌋₊, log p / p) / log y +
        ∫ t in y..x, (∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p) / (t * log t ^ 2) := by sorry
end LL_Decomp1528b
