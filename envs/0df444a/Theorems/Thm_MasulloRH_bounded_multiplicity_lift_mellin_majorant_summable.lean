-- Prove2me | Theorems.Thm_MasulloRH_bounded_multiplicity_lift_mellin_majorant_summable
-- name    : MasulloRH.bounded_multiplicity_lift_mellin_majorant_summable
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:40:53.285048+00:00
-- url     : https://prove2.me/theorems/03337f2d-db8e-433a-97ea-50325ea2cb24
-- title:
--   Summability of the scalar expression (10.4.2.34) at zeros of bounded multiplicity
-- statement:
--   Fix a multiplicity cap D and an admissible rational test. Over the actual interior zeta zeros of multiplicity n at most D, the sum of the absolute logarithmic Mellin moments of orders d<n, multiplied by n·2^(n−1), is summable. Its square, as displayed in (10.4.2.34), is summable as well. The cap is arbitrary but fixed. This is a scalar bound on the Mellin coefficients.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen draft, (10.4.2.34) on p. 464, referring to Theorem 10.3.2.1 on pp. 453–455. Rational specialization to the contribution from interior zeta zeros of multiplicity at most D.

import Definitions.Def_MasulloRH_RationalTrace
open MeasureTheory MasulloRH

theorem MasulloRH.bounded_multiplicity_lift_mellin_majorant_summable (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) (α : ℝ) (hα : 0 < α) (D : ℕ) :
    let n := fun ρ : ZetaZerosInTraceStrip α => analyticOrderNatAt riemannZeta (ρ:ℂ)
    let M := fun (ρ : ZetaZerosInTraceStrip α) (d : ℕ) =>
      ‖∫ y : ℝ, φ (Real.exp y) * (y:ℂ)^d * Complex.exp (((ρ:ℂ)-1/2)*y)‖
    let B := fun ρ => if n ρ ≤ D then
      (n ρ : ℝ) * 2^(n ρ - 1) * ∑ d ∈ Finset.range (n ρ), M ρ d else 0
    Summable B ∧ Summable (fun ρ => B ρ ^ 2) := by sorry
