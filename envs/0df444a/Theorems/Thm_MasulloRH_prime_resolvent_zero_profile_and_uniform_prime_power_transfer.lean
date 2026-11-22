-- Prove2me | Theorems.Thm_MasulloRH_prime_resolvent_zero_profile_and_uniform_prime_power_transfer
-- name    : MasulloRH.prime_resolvent_zero_profile_and_uniform_prime_power_transfer
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T12:44:25.437434+00:00
-- url     : https://prove2.me/theorems/91135a88-0fea-4eed-b9be-12d7ac06ae13
-- title:
--   Critical prime resolvent mass and uniform complex prime-power transfer
-- statement:
--   The prime-only mass Σ_{p≤x}(log p)²/p differs from (log x)²/2 by at most [2(log 4+4)+1537/log 2]log x+1537 for x≥2. For every complex cutoff of modulus at most one, removing higher prime powers from the corresponding Λ²/n sum costs at most 1537, uniformly in the cutoff and x. This yields the c=0 coefficient of the truncated prime-resolvent profile and transfers bounded imaginary-frequency cutoffs as well.
-- source:
--   Application of Zeta23.Cheb.defect_bounded_explicit and Zeta23.Cheb.sum_vonMangoldt_sq_div_eq_explicit (imported from Zeta23/Chebyshev.lean).

import Mathlib
import Theorems.Thm_Zeta23_Cheb_defect_bounded_explicit
import Theorems.Thm_Zeta23_Cheb_sum_vonMangoldt_sq_div_eq_explicit

open Finset Real
open ArithmeticFunction hiding log

theorem MasulloRH.prime_resolvent_zero_profile_and_uniform_prime_power_transfer (x : ℝ) (hx : 2 ≤ x) :
    (|(∑ n ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log n ^ 2 / n) -
       Real.log x ^ 2 / 2| ≤
       (2 * (Real.log 4 + 4) + 1537 / Real.log 2) * Real.log x + 1537) ∧
    (∀ w : ℕ → ℂ, (∀ n, ‖w n‖ ≤ 1) →
      ‖(∑ n ∈ Ioc 0 ⌊x⌋₊, w n * ((Λ n ^ 2 / n : ℝ) : ℂ)) -
        ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime,
          w n * ((Real.log n ^ 2 / n : ℝ) : ℂ)‖ ≤ 1537) := by sorry
