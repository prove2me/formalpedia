-- Prove2me | Theorems.Thm_MasulloRH_verified_square_prime_energy_prefix
-- name    : MasulloRH.verified_square_prime_energy_prefix
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:40:33.548585+00:00
-- url     : https://prove2.me/theorems/9f4e3766-854e-48ba-a52b-0dbea1443731
-- title:
--   Two explicit finite verifications for square-sampled prime energy and a general height certificate
-- statement:
--   For the square-sampled corrected prime-ramp energy E(N), every initial sum through N=100,000 is at most 63 and every initial sum through N=10,000,000 is at most 76. More generally, if zeros up to height 5/2+2M have real part at most 1/2 and 2(10+log M)(N+3) ≤ 5/2+2M−1, then E(N) ≤ 8. The first bound uses the critical-strip bound in the high-ordinate part of the exact formula. The second also uses the Prove2Me library bound β≤0.8749570698.
-- source:
--   Finite-prefix advance on MasulloRH.finite_square_prime_energy_cap (b41359f9). Uses the exact integrated prime-ramp formula b30beb93, the critical-line verification through height 100000, the reference-mass bound, and, for the ten-million bound, TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound (3a8f3264).

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
set_option autoImplicit false

open Finset ArithmeticFunction MeasureTheory Set
namespace MasulloRH

theorem verified_square_prime_energy_prefix :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let E (N : ℕ) := ∑ n ∈ range N, let k := (n:ℝ)+4; (G (k^2))^2/(k^3*(1+Real.log k)^2)
    (∀ N ≤ 100000, E N ≤ 63) ∧ (∀ N ≤ 10000000, E N ≤ 76) ∧
      ∀ (M N : ℕ), 1≤M →
        (∀ z : ZetaZerosInTraceStrip (1/2), |z.val.im| ≤ 5/2+2*(M:ℝ) → z.val.re ≤ 1/2) →
        2*(10+Real.log M)*((N:ℝ)+3) ≤ 5/2+2*(M:ℝ)-1 → E N ≤ 8 := by sorry

end MasulloRH
