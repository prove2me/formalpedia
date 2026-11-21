-- Prove2me | Theorems.Thm_MasulloRH_cofinal_rational_theta_gram_interval_tables
-- name    : MasulloRH.cofinal_rational_theta_gram_interval_tables
-- status  : Open
-- author  : @pragyan
-- created : 2026-11-21T04:01:44.165329+00:00
-- url     : https://prove2.me/theorems/7f59c68d-29e6-404c-a754-27288c412b6c
-- title:
--   Open rational interval tables certifying a strict finite theta Gram margin
-- statement:
--   For arbitrarily large n, choose finitely many rational shifts and coefficients in Q+iQ for the dyadic theta translates, and set δ=1/[16(n+1)]. Form the augmented function list u consisting of the normalized Gaussian pulse followed by the translates, and the coefficient vector d=(1,−a₁,…,−aₘ). Let Γ be its endpoint-weighted Gram matrix at center 3/4 and half-width 1/4−δ.
--
--   The proposed input is a finite rational complex matrix Q and a rational error η≥0 such that every Gram entry is enclosed and the rational upper certificate has a strict margin:
--
--   $$|\Gamma_{ij}-Q_{ij}|\le\eta,\qquad
--   \operatorname{Re}(d^*Qd)+\eta\left(\sum_i(|\operatorname{Re}d_i|+|\operatorname{Im}d_i|)\right)^2<\delta/2.$$
--
--   The scalar certificate uses only rational arithmetic once the finitely many integral enclosures have been established. No inverse, positive-definiteness assertion, or zero-location premise is required. This is an OPEN cofinal family of numerical certificates, not a claim that a fixed finite table proves the infinite approximation assertion. The error allowance records how accurate the individual integral enclosures need to be for the chosen coefficients.
-- source:
--   New finite interval-certificate interface for MasulloRH.cofinal_rational_theta_gram_certificates, https://prove2.me/theorems/7c5cdf67-e5d6-4b32-9576-87775aefd2d2. Its exact Gram identity and integrability are proved by MasulloRH.finite_theta_approximation_excludes_rectangle_zeros, https://prove2.me/theorems/8481aa5d-a121-4938-8de2-17c814da37b2. Endpoint norm: Masullo, The Music of the Primes, Definition9.2.2.1 and equation9.2.2.4, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=412. The quantitative interval-matrix interface is a new sufficient criterion, not an assertion extracted from the manuscript.

import Definitions.Def_MasulloRH_GaussianThetaApproximation
open MasulloRH.GaussianApproximation MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false

theorem MasulloRH.cofinal_rational_theta_gram_interval_tables :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ)
      (R : Fin (m+1) → Fin (m+1) → ℚ × ℚ) (η : ℚ), 0 ≤ η ∧
      let δ : ℝ := 1/(16*((n:ℝ)+1))
      let u : Fin (m+1) → ℝ → ℂ := Fin.cons (pulse n)
        (fun i x => theta (x-(y i:ℝ)))
      let d : Fin (m+1) → ℂ := Fin.cons 1
        (fun i => -(((a i).1:ℂ)+((a i).2:ℂ)*Complex.I))
      let Q : Fin (m+1) → Fin (m+1) → ℂ :=
        fun i j => ((R i j).1:ℂ)+((R i j).2:ℂ)*Complex.I
      (∀ i j, ‖(∫ x : ℝ, (Real.exp (2*(3/4)*x+2*(1/4-δ)*|x|):ℂ) *
        conj (u i x) * u j x) - Q i j‖ ≤ (η:ℝ)) ∧
      (∑ i, ∑ j, conj (d i)*d j*Q i j).re +
        (η:ℝ) * (∑ i, (|(d i).re|+|(d i).im|))^2 < δ/2 := by sorry
