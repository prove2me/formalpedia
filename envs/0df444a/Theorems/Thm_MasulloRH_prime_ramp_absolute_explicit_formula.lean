-- Prove2me | Theorems.Thm_MasulloRH_prime_ramp_absolute_explicit_formula
-- name    : MasulloRH.prime_ramp_absolute_explicit_formula
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:05:33.925384+00:00
-- url     : https://prove2.me/theorems/b30beb93-f39f-4f6e-b456-e7a7c5c263cc
-- title:
--   The corrected prime ramp has an absolute zero expansion and attains the verified zero-free exponent
-- statement:
--   For G(x)=Σₙ≤ₓ Λ(n)(x/n−1)₊−x(log x−1−γ), let K(x,ρ)=mρ x^(ρ−1)/(ρ(ρ−1)). At every x≥2, G(x)/x equals −Σρ K(x,ρ) plus the integral from x to infinity of [log(2π)+(1/2)log(1−t⁻²)]/t². The same finite constant C=Σρ |K(1,ρ)|+|log(2π)|+|log(1/2)| gives |G(x)|≤C x^θ for every nonnegative upper bound θ on nontrivial zero real parts. In particular the unconditional campaign exponent 0.8749570698 holds with no loss at the endpoint and no logarithmic factor.
-- source:
--   Integrates the campaign increment theorem 46bfb4c3 (https://prove2.me/theorems/46bfb4c3-d0d0-4f45-8cc0-78976bcb1803). Adapted the Mellin transform and pole subtraction from the masullo-night contribution 2850659b on MasulloRH.zero_free_right. The absolute von Mangoldt Dirichlet series extends this transform to Re s>1. A rescaled exponential average fixes the integration constant using analyticity at 1. Uses TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound for the unconditional numerical specialization.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
set_option autoImplicit false

open Finset ArithmeticFunction MeasureTheory Set
namespace MasulloRH

theorem prime_ramp_absolute_explicit_formula :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let K (x : ℝ) (ρ : ZetaZerosInTraceStrip (1/2)) :=
      (analyticOrderNatAt riemannZeta ρ.val : ℂ) * (x:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1))
    let C : ℝ := (∑' ρ : ZetaZerosInTraceStrip (1/2),‖K 1 ρ‖) + (|Real.log (2*Real.pi)|+|Real.log (1/2)|)
    (∀ x : ℝ, 2≤x →
      ((G x/x:ℝ):ℂ) = -(∑' ρ : ZetaZerosInTraceStrip (1/2),K x ρ) +
        ((∫ t in Ioi x,(Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)))/t^2 : ℝ):ℂ)) ∧
    (∀ θ : ℝ, 0≤θ → (∀ ρ : ZetaZerosInTraceStrip (1/2),ρ.val.re≤θ) →
      ∀ x : ℝ, 2≤x → |G x|≤C*x^θ) ∧
    (∀ x : ℝ, 2≤x → |G x|≤C*x^(0.8749570698:ℝ)) := by sorry

end MasulloRH
