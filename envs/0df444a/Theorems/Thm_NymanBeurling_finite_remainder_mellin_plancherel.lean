-- Prove2me | Theorems.Thm_NymanBeurling_finite_remainder_mellin_plancherel
-- name    : NymanBeurling.finite_remainder_mellin_plancherel
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:13:58.452659+00:00
-- url     : https://prove2.me/theorems/516ee0b8-961c-4204-8d6b-cca1ccbeedac
-- title:
--   The exact critical-line Plancherel identity for finite Bagchi remainder sums
-- statement:
--   For a finite collection of complex coefficients let R(m)=1−∑_d c_d (m mod d)/d, with positive denominators d≥2. On the critical line s=1/2−it put F(t)=[1−ζ(s)∑_d c_d(d⁻¹−d^(−s))]/s. Then |F|² is integrable and
--   ∫_ℝ |F(t)|² dt = 2π ∑_{m≥1} |R(m)|²/[m(m+1)].
--   The denominator offset k+2 in Lean agrees with the discrete certificate and also handles arbitrary finite damped Möbius polynomials. This identity is unconditional, including at the ordinates of critical-line zeros.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte’s Hilbert space reformulation of the Riemann hypothesis, Theorems 1, 2 and 5, especially identity (4) and the isometric step-function identification, https://arxiv.org/pdf/math/0607733 . The proof imports the established Prove2Me MellinParseval theorem ac289eb0.

import Mathlib

open MeasureTheory

theorem NymanBeurling.finite_remainder_mellin_plancherel (S : Finset ℕ) (c : ℕ→ℂ) :
    let s := fun t : ℝ => (1/2:ℂ) - (t:ℂ)*Complex.I
    let F := fun t : ℝ => (1 - (∑ k ∈ S, c k * (((k+2:ℕ):ℂ)⁻¹ - ((k+2:ℕ):ℂ)^(-s t))) * riemannZeta (s t)) / s t
    Integrable (fun t : ℝ => ‖F t‖^2) ∧
      (∫ t : ℝ, ‖F t‖^2) = 2*Real.pi * ∑' n : ℕ,
        ‖1-∑ k ∈ S, c k * ((((n+1)%(k+2):ℕ):ℂ)/((k+2:ℕ):ℂ))‖^2 / ((n+1:ℝ)*(n+2:ℝ)) := by sorry
