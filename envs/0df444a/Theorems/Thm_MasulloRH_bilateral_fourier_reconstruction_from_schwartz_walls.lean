-- Prove2me | Theorems.Thm_MasulloRH_bilateral_fourier_reconstruction_from_schwartz_walls
-- name    : MasulloRH.bilateral_fourier_reconstruction_from_schwartz_walls
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T04:05:35.903251+00:00
-- url     : https://prove2.me/theorems/23524bc8-a1d2-4f7d-b06c-084f1a736f58
-- title:
--   Reconstruction of a common weighted Fourier inverse from two strip boundaries
-- statement:
--   Let a function be continuous on a closed vertical strip and holomorphic in the interior. Suppose it tends uniformly to zero on a sequence of horizontal ends in both directions. If each vertical boundary profile is an L¹ Fourier transform times a Schwartz multiplier with polynomial L² control, then the two profiles reconstruct a single continuous kernel with exponential L¹ and polynomial-exponential L² control, including the exact boundary Fourier identities.
-- source:
--   Fourier strip reconstruction used for spectral synthesis in the rational specialization of Masullo, The Music of the Primes, Chapters 9–10. Standard Fourier inversion and the Cauchy integral theorem.

import Mathlib
open Set MeasureTheory Filter FourierTransform
open scoped Topology FourierTransform SchwartzMap

theorem MasulloRH.bilateral_fourier_reconstruction_from_schwartz_walls (b p : ℝ) (hb : 0≤b) (hp : 0≤p) (Q : ℂ→ℂ) :
    let v := fun (u t : ℝ) => (u:ℂ)+(t:ℂ)*Complex.I
    let P := fun (u ξ : ℝ) => Q (v u ((-2*Real.pi)*ξ))
    let tilt := fun (u : ℝ) (q : ℝ→ℂ) (x : ℝ) => (Real.exp (u*x):ℂ)*q x
    ContinuousOn Q {s : ℂ | |s.re|≤b} →
    DifferentiableOn ℂ Q {s : ℂ | |s.re|<b} →
    (∃ T e : ℕ→ℝ, Tendsto T atTop atTop ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ (n : ℕ) (u : ℝ), |u|≤b → ‖Q (v u (T n))‖≤e n ∧ ‖Q (v u (-T n))‖≤e n) →
    (∀ u : ℝ, |u|=b → ∃ f : ℝ→ℂ, ∃ m : 𝓢(ℝ,ℂ), Integrable f ∧
      MemLp (fun x : ℝ => (1+|x|)^p*‖f x‖) 2 volume ∧ ∀ ξ, P u ξ=(𝓕 f) ξ*m ξ) →
    ∃ q : ℝ→ℂ, Continuous q ∧ Integrable (fun x : ℝ => Real.exp (b*|x|)*‖q x‖) ∧
      MemLp (fun x : ℝ => (1+|x|)^p*(Real.exp (b*|x|)*‖q x‖)) 2 volume ∧
      ∀ u : ℝ, |u|=b → tilt u q=𝓕⁻ (P u) ∧ 𝓕 (tilt u q)=P u := by sorry
