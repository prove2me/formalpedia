-- Prove2me | Theorems.Thm_MasulloRepair_EulerScale_finite_prime_blaschke_product_delay_bound
-- name    : MasulloRepair.EulerScale.finite_prime_blaschke_product_delay_bound
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T23:41:05.677143+00:00
-- url     : https://prove2.me/theorems/29a009fc-afba-4b30-a13b-5ae7f4c31af2
-- title:
--   A quantitative delay limit for finite rational Euler Blaschke products
-- statement:
--   Let $S$ be a nonempty finite set of rational primes and fix $\kappa>0$. Put
--
--   $$\theta_S=\sum_{p\in S}\log p,\qquad B_S(w)=\prod_{p\in S}\frac{e^{-w\log p}-p^{-\kappa}}{1-p^{-\kappa}e^{-w\log p}}.$$
--
--   Then every $z\in\mathbb C$ with $\Re z\ge0$ satisfies
--
--   $$\left|B_S\left(\frac{z}{\theta_S}\right)-e^{-z}\right|\le\frac{2|z|}{1-2^{-\kappa}}\frac{\sum_{p\in S}p^{-\kappa}\log p}{\theta_S}.$$
--
--   The estimate includes the imaginary boundary and applies to every nonempty finite prime set. Its right-hand side isolates the weighted average that controls the reciprocal log-primorial scaling limit of these explicit Euler factors. The result provides a quantitative comparison for the rational Euler Hardy model without any hypothesis about zeta zeros.
--
--   **Formalization Note.** The formal target is this finite estimate. A limit theorem, the associated operator limits, and identification with the manuscript's geometric construction are separate assertions.
-- source:
--   Original finite-product estimate developed for the Masullo mission, extending the moving-probe calculation by Yi in mission discussion comment 2f2f1d62-3a43-44d0-a05b-3ddd9702b1d0. Discussion board: https://prove2.me/missions/Masullo%253A_The_Music_of_the_Primes_%E2%80%94_Riemann_Hypothesis_specialization/discussions . The source trace target remains https://prove2.me/theorems/349e4bbd-c20f-49b2-8bde-edec03c051a8 . This is a new supporting estimate, not a theorem attributed to Masullo’s manuscript.

import Mathlib

open scoped BigOperators
open Complex Set

theorem MasulloRepair.EulerScale.finite_prime_blaschke_product_delay_bound (s : Finset ℕ)
    (hs : s.Nonempty) (hp : ∀ p ∈ s, Nat.Prime p) (κ : ℝ) (hκ : 0 < κ)
    (z : ℂ) (hz : 0 ≤ z.re) :
    let θ : ℝ := ∑ p ∈ s, Real.log p
    ‖(∏ p ∈ s,
        (Complex.exp (-((Real.log p / θ : ℝ) : ℂ) * z) -
          (Real.exp (-κ * Real.log p) : ℂ)) /
        (1 - (Real.exp (-κ * Real.log p) : ℂ) *
          Complex.exp (-((Real.log p / θ : ℝ) : ℂ) * z))) - Complex.exp (-z)‖ ≤
      (2 * ‖z‖ / (1 - Real.exp (-κ * Real.log 2))) *
        ((∑ p ∈ s, Real.exp (-κ * Real.log p) * Real.log p) / θ) := by sorry
