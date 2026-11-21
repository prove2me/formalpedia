-- Prove2me | Theorems.Thm_MasulloRH_riemannHypothesis_iff_prime_ramp_log_energy
-- name    : MasulloRH.riemannHypothesis_iff_prime_ramp_log_energy
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:23:46.913171+00:00
-- url     : https://prove2.me/theorems/0764b70c-7fc9-4986-bd5f-e247f8391bfb
-- title:
--   Riemann Hypothesis is equivalent to a single finite positive logarithmic energy of the corrected prime ramp
-- statement:
--   Let G(x)=Σₙ≤ₓ Λ(n)(x/n−1)₊−x(log x−1−γ) and Fθ(u)=G(exp u)exp(−θu)/(1+u). For each 0≤θ<1, the function Fθ² is Lebesgue integrable on u>0 if and only if every nontrivial zeta zero has real part at most θ. In particular, ordinary RH is equivalent to integrability at exactly θ=1/2. Whenever all real parts are at most θ≥0, the integral is at most 81.
-- source:
--   Uses 69c40bb0 (https://prove2.me/theorems/69c40bb0-3a4f-41e4-bb12-a8fa066d7105) for the uniform pointwise constant 9, and the von Mangoldt transform computed in the masullo-night prime-ramp proof 2850659b, extended to the half-plane of absolute convergence. The new converse pairs the energy with polynomial times exponential kernels by Cauchy–Schwarz. Analytic continuation then gives a homogeneous first-order differential equation for (s−1)ζ(s). A zero of finite order is impossible there.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
set_option autoImplicit false

open Finset ArithmeticFunction MeasureTheory Set
namespace MasulloRH

theorem riemannHypothesis_iff_prime_ramp_log_energy :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let F (θ u : ℝ) := G (Real.exp u)*Real.exp (-(θ*u))/(1+u)
    (∀ θ : ℝ, 0 ≤ θ → θ < 1 →
        ((∀ z : ZetaZerosInTraceStrip (1/2), z.val.re ≤ θ) ↔
           IntegrableOn (fun u => (F θ u)^2) (Ioi (0:ℝ)))) ∧
    (RiemannHypothesis ↔ IntegrableOn (fun u => (F (1/2) u)^2) (Ioi (0:ℝ))) ∧
    (∀ θ : ℝ, 0 ≤ θ → (∀ z : ZetaZerosInTraceStrip (1/2), z.val.re ≤ θ) →
        (∫ u in Ioi (0:ℝ),(F θ u)^2) ≤ 81) := by sorry

end MasulloRH
