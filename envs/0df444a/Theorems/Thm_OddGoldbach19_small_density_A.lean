-- Prove2me | Theorems.Thm_OddGoldbach19_small_density_A
-- name    : OddGoldbach19.small_density_A
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T16:11:02.111991+00:00
-- url     : https://prove2.me/theorems/d2bf1a8e-15a8-49ee-b2cd-46bb48bc90dd
-- title:
--   One-ninth additive density through logarithmic cutoff 26
-- statement:
--   Let A be the existing shared Schnirelmann additive set B+B, where B encodes odd primes as (p-3)/2. For every positive natural number N satisfying log(2N+6)<=26, at least N/9 of the positive integers at most N belong to A. Logarithms are natural. This is a bounded-range density assertion only; it does not assert the same density at all N or a complete 19-prime campaign endpoint. The cutoff26 and finite thresholds are derived in this development.
-- source:
--   Riesel and Vaughan, On sums of primes, Arkiv for Matematik21(1983), Lemma7, p58, https://doi.org/10.1007/BF02384300 ; affine finite counting refinement OddGoldbach19.small_count_A and existing Rosser–Schoenfeld theta lower estimate. Cutoff26 is derived locally.

import Mathlib
import Definitions.Def_Schnir_defs
open Classical

theorem OddGoldbach19.small_density_A (N : ℕ) (hN : 1 ≤ N)
    (hlog26 : Real.log ((2 * N + 6 : ℕ) : ℝ) ≤ 26) :
    (N : ℝ) / 9 ≤ (((Finset.Ioc 0 N).filter (fun a => a ∈ Schnir.A)).card : ℝ) := by sorry
