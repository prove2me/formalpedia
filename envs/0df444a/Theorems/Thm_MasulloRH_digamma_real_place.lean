-- Prove2me | Theorems.Thm_MasulloRH_digamma_real_place
-- name    : MasulloRH.digamma_real_place
-- status  : Proved
-- author  : @Calvin Yost-Wolff
-- created : 2026-11-21T00:28:55.893176+00:00
-- url     : https://prove2.me/theorems/0f82fc90-5a06-4114-9a31-b82a1b80e123
-- title:
--   The digamma term equals the negative real-place term in the rational trace formula
-- statement:
--   Let φ be a smooth complex-valued test function with compact support contained in the positive real half-line and φ(1) = 0. Put Φ(s) = ∫₀^∞ φ(t)t^s dt/t. The integrands on both sides of the following identity are absolutely integrable: (1/(2π))∫_ℝ Φ(ir)(Re ψ(1/4 + ir/2) − log π) dr = −∫₁^∞ (φ(t) + φ(t⁻¹))√t/(t² − 1) dt. Here ψ is the digamma function Γ′/Γ.
-- source:
--   Real-place normalization for Masullo, The Music of the Primes, Theorem 12.5.1.1, pp. 519–520, rational specialization. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf Gauss digamma integral: NIST DLMF §5.9(ii), https://dlmf.nist.gov/5.9.E16. Fourier convention: https://github.com/anthropics/formal-math/blob/main/zeta23/Zeta23/ExplicitFormula.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.ContDiff.Basic

open MeasureTheory Set
open scoped ContDiff

theorem MasulloRH.digamma_real_place (φ : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ φ)
    (hCompact : HasCompactSupport φ) (hPositive : tsupport φ ⊆ Ioi 0) (hOne : φ 1 = 0) :
    let spectral : ℝ → ℂ := fun r => mellin φ (Complex.I * r) *
      (((Complex.digamma (1 / 4 + (r : ℂ) * Complex.I / 2)).re - Real.log Real.pi : ℝ) : ℂ)
    let geometric : ℝ → ℂ := fun t =>
      (φ t + φ t⁻¹) * ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ)
    Integrable spectral ∧ IntegrableOn geometric (Ioi 1) ∧
      (1 / (2 * (Real.pi : ℂ))) * (∫ r : ℝ, spectral r) =
        -(∫ t in Ioi (1 : ℝ), geometric t) := by sorry
