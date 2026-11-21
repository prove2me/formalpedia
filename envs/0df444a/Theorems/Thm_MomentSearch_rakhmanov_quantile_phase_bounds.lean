-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_quantile_phase_bounds
-- name    : MomentSearch.rakhmanov_quantile_phase_bounds
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-20T23:37:29.673927+00:00
-- url     : https://prove2.me/theorems/5188ebde-f5d5-45b0-a575-bb47e66f4f71
-- title:
--   Local bounds for the equilibrium cosine phase at a midpoint quantile
-- statement:
--   For integers $1\le k<N$, let $r=\sqrt{1-k^2/N^2}$ and let $\rho(z)=(N/\pi)\arctan((N/k)\sqrt{(r^2-z^2)_+})$. Set $f(z)=\cos(\pi\int_z^1\rho(t)\,dt)$. For each $|x|<r$ there is a zero $y$ in the support interior and a scale $\rho(x)\le M\le N/2$, $M>0$, with $|x-y|\le 2/M$. For $q(z)=|f(z)|/|z-y|$, continued at $y$ by $\pi\rho(y)$, the bounds are
--   $$q(x)\ge M/4,\qquad q(z)\max(1,M|z-y|)\le 4M\quad (|z|\le1).$$
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, Annals of Mathematics 165 (2007), §2.1–2.2, https://annals.math.princeton.edu/2007/165-1/p03

import Mathlib

theorem MomentSearch.rakhmanov_quantile_phase_bounds (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    ∀ x ∈ Set.Ioo (-r) r, ∃ M y : ℝ,
      y ∈ Set.Ioo (-r) r ∧ f y = 0 ∧ 0 < M ∧ M ≤ (N : ℝ) / 2 ∧
      |x-y| ≤ 2/M ∧ ρ x ≤ M ∧
      let q : ℝ → ℝ := fun z => if z = y then Real.pi * ρ y else |f z| / |z-y|
      M / 4 ≤ q x ∧ ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        q z * max 1 (M * |z-y|) ≤ 4*M := by sorry
