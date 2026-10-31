-- Prove2me | Theorems.Thm_OddGoldbach19_small_count_A
-- name    : OddGoldbach19.small_count_A
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T16:07:49.11698+00:00
-- url     : https://prove2.me/theorems/bf6adae1-b1db-41d1-af22-dae9ff9fea2f
-- title:
--   A three-halves prime-counting bound for the Schnirelmann additive set
-- statement:
--   Let A be the shared set B+B, where B consists of (p-3)/2 for odd primes p. For every natural number N at least 5, write A(N) for the number of positive integers at most N belonging to A, and pi(x) for the number of primes at most x. Then 3*pi(2N+1) <= 2*A(N)+12. The finite correction 12 accounts for excluding primes below 11. This is an explicit small-range counting input; it does not assert a complete 19-prime representation theorem.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Arkiv for Matematik21(1983), pp45–74, Lemma7 proof on p58: union of p+3 and p+5, excluding three consecutive odd primes. https://doi.org/10.1007/BF02384300 . The affine A-count statement and finite correction are derived here.

import Mathlib
import Definitions.Def_Schnir_defs
open Classical

theorem OddGoldbach19.small_count_A (N : ℕ) (hN : 5 ≤ N) :
    3 * Nat.primeCounting (2 * N + 1) ≤
      2 * ((Finset.Ioc 0 N).filter (fun a => a ∈ Schnir.A)).card + 12 := by sorry
