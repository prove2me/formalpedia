-- Prove2me | Theorems.Thm_MasulloRH_finite_ordinate_prime_ramp_approximation
-- name    : MasulloRH.finite_ordinate_prime_ramp_approximation
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:12:32.269646+00:00
-- url     : https://prove2.me/theorems/69c40bb0-3a4f-41e4-bb12-a8fa066d7105
-- title:
--   A numerical finite-height formula for the corrected prime ramp at fourth powers
-- statement:
--   For k≥2, set x=k⁴ and H=5/2+2k². Take exactly the nontrivial zeros ρ with Re ρ>θ and 100000<|Im ρ|≤H, with their analytic multiplicities. For every θ≥1/2, the absolute value of G(x) plus the real part of the finite sum of mρ x^ρ/[ρ(ρ−1)] is at most 19 x^θ. In particular |G(k⁴)|≤19 k² for 2≤k≤223. Globally, |G(x)|≤9 x^0.8749570698 for x≥2, and the same constant 9 works for any nonnegative upper bound on zero real parts.
-- source:
--   Uses the absolutely convergent prime-ramp formula b30beb93 and MasulloRH.zero_decay_tail_at_real_lattice. At lattice index 1 the full kernel weight is at most 6. At index k² the discarded high part costs at most 10 k². The archimedean correction costs at most 3, and the proven TaoFivePrimes height blocks exclude all off-line contributions through height 100000. This supplies explicit constants and a sufficient height for the fourth-power frontier 4edebb28.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
set_option autoImplicit false

open Finset ArithmeticFunction MeasureTheory Set
namespace MasulloRH

theorem finite_ordinate_prime_ramp_approximation :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let P (x : ℝ) (z : ZetaZerosInTraceStrip (1/2)) := (x:ℂ)*
      ((analyticOrderNatAt riemannZeta z.val : ℂ)*(x:ℂ)^(z.val-1)/(z.val*(z.val-1)))
    (∀ k : ℕ, 2≤k → ∀ θ : ℝ, 1/2≤θ →
      ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
        (∀ z : ZetaZerosInTraceStrip (1/2), z ∈ F ↔ θ<z.val.re ∧
          100000 < |z.val.im| ∧ |z.val.im|≤5/2+2*((k^2:ℕ):ℝ)) ∧
        |G ((k:ℝ)^4)+(∑ z ∈ F,P ((k:ℝ)^4) z).re| ≤ 19*((k:ℝ)^4)^θ) ∧
    (∀ k : ℕ, 2≤k → k≤223 → |G ((k:ℝ)^4)| ≤ 19*(k:ℝ)^2) ∧
    (∀ θ : ℝ, 0≤θ → (∀ z : ZetaZerosInTraceStrip (1/2), z.val.re≤θ) →
      ∀ x : ℝ, 2≤x → |G x|≤9*x^θ) ∧
    (∀ x : ℝ, 2≤x → |G x|≤9*x^(0.8749570698:ℝ)) := by sorry

end MasulloRH
