-- Prove2me | Theorems.Thm_MasulloAudit_mellin_kernel_projection_limit
-- name    : MasulloAudit.mellin_kernel_projection_limit
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:55:10.291451+00:00
-- url     : https://prove2.me/theorems/4e05fabd-d303-4530-94e2-8760e310f10f
-- title:
--   The truncated Mellin-kernel projections converge to the common kernel, with an explicit positive-width counterexample
-- statement:
--   In the Sobolev-degree-zero logarithmic realization for $I=[-1,1]$, the Hilbert norm is $L^2(e^{2|x|}dx)$. An exponentially Schwartz test with Mellin transform $s e^{s^2}$ has a single simple zero at the origin. Evaluation there has unit Riesz vector $v(x)=e^{-2|x|}$. For every $T>0$, the kernel intersection in (9.3.2.10) equals $v^\perp$ and its orthogonal projection annihilates $v$, disproving the asserted strong convergence to the identity. For every increasing exhaustion of a countable family of Riesz rows by finite sets, the finite-span projections converge strongly to the closed-span projection and the kernel projections converge strongly to the common-kernel projection. The latter is the identity exactly when every row vanishes.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Theorem 9.3.2.6 and equation (9.3.2.10), p. 426, applied in Theorem 10.2.2.1, p. 445. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=426. Uses the positive-width norm in Definition 9.2.2.1, the checked exponential-integral formula e2170362, and Mathlib’s monotone projection convergence theorem.

import Mathlib
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace SchwartzMap
local notation "W" => Lp ℂ 2 (Measure.withDensity (volume : Measure ℝ) (fun x : ℝ => ENNReal.ofReal (Real.exp (2*|x|))))

theorem MasulloAudit.mellin_kernel_projection_limit :
    (∃ (φ : ℝ → ℂ) (v : W),
      (∀ a : ℝ, ∃ g : 𝓢(ℝ,ℂ), ∀ x : ℝ, g x = Complex.exp ((a:ℂ)*x) * φ (Real.exp x)) ∧
      (∀ s : ℂ, HasMellin φ s (s * Complex.exp (s^2))) ∧
      (∀ s : ℂ, mellin φ s = 0 ↔ s = 0) ∧ analyticOrderAt (mellin φ) 0 = 1 ∧
      (v : ℝ → ℂ) =ᵐ[volume] (fun x : ℝ => ((Real.exp (-2*|x|):ℝ):ℂ)) ∧
      ⟪v,v⟫_ℂ = 1 ∧
      (∀ u : W, ⟪v,u⟫_ℂ = ∫ x : ℝ, u x) ∧
      (let K := (ℂ ∙ v)ᗮ
       (∀ T : ℝ, 0 < T → ∀ u : W, u ∈ K ↔
         ∀ s : ℂ, mellin φ s = 0 → |s.im| ≤ T →
           ∀ j : ℕ, j < analyticOrderNatAt (mellin φ) s →
             (∫ x : ℝ, ((x:ℂ)^j * Complex.exp (s*x)) * u x) = 0) ∧
       K.starProjection v = 0 ∧
       ¬ Tendsto (fun _ : ℝ => K.starProjection v) atTop (𝓝 v))) ∧
    (∀ (ι : Type) (v : ι → W) (F : ℕ → Finset ι), Monotone F → (∀ i, ∃ n, i ∈ F n) →
      let U (n : ℕ) := (Submodule.span ℂ (v '' (F n : Set ι))).topologicalClosure
      let V := (Submodule.span ℂ (Set.range v)).topologicalClosure
      (∀ u : W, u ∈ Vᗮ ↔ ∀ i, ⟪v i,u⟫_ℂ = 0) ∧
      (∀ u : W, Tendsto (fun n => (U n).starProjection u) atTop (𝓝 (V.starProjection u))) ∧
      (∀ u : W, Tendsto (fun n => (U n)ᗮ.starProjection u) atTop (𝓝 (Vᗮ.starProjection u))) ∧
      ((∀ u : W, Tendsto (fun n => (U n)ᗮ.starProjection u) atTop (𝓝 u)) ↔ ∀ i, v i = 0)) := by sorry
