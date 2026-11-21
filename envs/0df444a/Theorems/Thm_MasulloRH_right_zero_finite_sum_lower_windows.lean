-- Prove2me | Theorems.Thm_MasulloRH_right_zero_finite_sum_lower_windows
-- name    : MasulloRH.right_zero_finite_sum_lower_windows
-- status  : Open
-- author  : @marozols
-- created : 2026-11-21T03:15:25.203183+00:00
-- url     : https://prove2.me/theorems/dcf44745-1ea1-4a32-a572-1cd7bccc4f61
-- title:
--   Cofinal lower windows for the finite right-hand zero sum of the prime ramp
-- statement:
--   For 1/2<θ<0.8749570698, find fixed positive δ and nonnegative C, and arbitrarily late integer starts K≥2. For every integer k between K and K^(1+δ)+1, put x=k⁴. The real part of the finite sum of mρ x^ρ/[ρ(ρ−1)] over exactly the zeros with θ<Re ρ and 100000<|Im ρ|≤5/2+2k² should be at least −C x^θ. All height cutoffs are fixed in advance. This is the remaining open oscillatory cancellation estimate.
-- source:
--   Exact finite-data question for MasulloRH.fourth_power_prime_ramp_upper_windows, 4edebb28. The numerical finite-height approximation bounds all lower-real-part zeros, all higher ordinates, and the archimedean term by 19 x^θ. No sign condition on individual terms is required.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
set_option autoImplicit false

open Finset ArithmeticFunction MeasureTheory Set
namespace MasulloRH

theorem right_zero_finite_sum_lower_windows :
    ∀ θ : ℝ, 1/2 < θ → θ < 0.8749570698 → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ m : ℕ, 2 ≤ m → ∃ J : ℕ, m ≤ J ∧
        ∀ k : ℕ, J ≤ k → (k:ℝ) ≤ (J:ℝ)^(1+δ)+1 →
          ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
            (∀ z : ZetaZerosInTraceStrip (1/2), z ∈ F ↔ θ < z.val.re ∧
              100000  <  |z.val.im| ∧ |z.val.im| ≤ 5/2+2*((k^2:ℕ):ℝ)) ∧
            let x := (k:ℝ)^4;
            -(C*x^θ)  ≤  (∑ z ∈ F,(x:ℂ)*((analyticOrderNatAt riemannZeta z.val : ℂ)*
              (x:ℂ)^(z.val-1)/(z.val*(z.val-1)))).re := by sorry

end MasulloRH
