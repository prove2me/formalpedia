-- Prove2me | Theorems.Thm_GRH_identity_progression_prime_weight_mellin_majorant
-- name    : GRH.identity_progression_prime_weight_mellin_majorant
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T01:45:01.713994+00:00
-- url     : https://prove2.me/theorems/c45e4136-ea1d-4062-953b-99627d5940fb
-- title:
--   The Mellin transform of the one-class prime-power majorant
-- statement:
--   For D≥0 and θ<1, A(x)=D x^θ+φ(q)ψ(x;q,1)−x is measurable and has convergent Mellin integrals for Re(s)>1. Its transform is D/(s−θ)−(P′(s)/P(s)+1)/s for the regularized product P of all character L-functions modulo q.
-- source:
--   Arithmetic reduction for GRH.centered_moebius_progression_bilinear_power_bound. The fixed-modulus equivalence is https://prove2.me/theorems/04e865ba-3dd7-43e6-9714-8e4d666e0b7c . Mathlib.NumberTheory.LSeries.SumCoeff and Mathlib.NumberTheory.Chebyshev.

import Definitions.Def_GRH_SplitPrimeLower

open GRH.SplitPrimeLower MeasureTheory GRH.OneSidedMoebius

theorem GRH.identity_progression_prime_weight_mellin_majorant (q : ℕ) [NeZero q] (D θ : ℝ) (hD : 0≤D) (hθ : θ<1) :
    Measurable (primeMajorant q D θ) ∧
    (∀ σ : ℝ, 1<σ → IntegrableOn (fun x : ℝ => primeMajorant q D θ x*x^(-σ-1)) (Set.Ioi 1)) ∧
    ∀ s : ℂ, 1<s.re → transform (primeMajorant q D θ) s =
      (D:ℂ)/(s-θ) - (logDeriv (regularProduct q) s+1)/s := by sorry
