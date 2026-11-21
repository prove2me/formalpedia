-- Prove2me | Theorems.Thm_MasulloRH_rectangular_average_multiplier_regularity
-- name    : MasulloRH.rectangular_average_multiplier_regularity
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T02:15:52.295333+00:00
-- url     : https://prove2.me/theorems/8c7669ac-b48e-468f-af17-318c6a1a9879
-- title:
--   Regularity of indented rectangle averages under bounded absolute averages
-- statement:
--   For complex kernels and multipliers on normalized product-measure rectangles, if the absolute kernel averages are uniformly bounded by C and the multiplier differs from q₀ by at most Eₙ almost everywhere in rectangle n, the indentation error is at most EₙC. If Eₙ tends to zero, the error tends to zero. At q₀ ≠ 0, the ordinary averages converge to L exactly when the indented averages converge to q₀L.
-- source:
--   Masullo, The Music of the Primes (20 November 2026 draft), Definition 12.1.1.1 and Proposition 12.2.2.2(4), equations (12.2.2.1–2), (12.2.2.22–25), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=508. Sufficient correction discussed on the Masullo Prove2Me mission, comment 07a458ac-9f06-48a7-9987-5f620feb9dd1.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

open Filter MeasureTheory
open scoped Topology ENNReal

theorem MasulloRH.rectangular_average_multiplier_regularity {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (U V : ℕ → Set X) :
    let R := fun n => U n ×ˢ V n
    let ν := fun n => ((μ.prod μ) (R n))⁻¹ • (μ.prod μ).restrict (R n)
    ∀ (K q : X × X → ℂ) (q₀ : ℂ) (E : ℕ → ℝ) (C : ℝ),
    (∀ n, Integrable K (ν n)) →
    (∀ n, Integrable (fun x => q x * K x) (ν n)) →
    (∀ n, 0 ≤ E n) →
    (∀ n, ∀ᵐ x ∂ν n, ‖q x - q₀‖ ≤ E n) →
    (∀ n, ∫ x, ‖K x‖ ∂ν n ≤ C) → Tendsto E atTop (𝓝 0) →
    let A := fun n => ∫ x, K x ∂ν n
    let B := fun n => ∫ x, q x * K x ∂ν n
    (∀ n, ‖B n - q₀ * A n‖ ≤ E n * C) ∧
    Tendsto (fun n => B n - q₀ * A n) atTop (𝓝 0) ∧
    (∀ L : ℂ, q₀ ≠ 0 → (Tendsto (fun n => B n) atTop (𝓝 (q₀ * L)) ↔
      Tendsto (fun n => A n) atTop (𝓝 L))) := by sorry
