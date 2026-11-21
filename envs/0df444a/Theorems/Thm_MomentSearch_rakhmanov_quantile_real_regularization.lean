-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_quantile_real_regularization
-- name    : MomentSearch.rakhmanov_quantile_real_regularization
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-21T00:03:05.80219+00:00
-- url     : https://prove2.me/theorems/5da39c37-1ebb-42b7-99bb-ba62c2cfd1e7
-- title:
--   Real regularization of the midpoint-quantile product
-- statement:
--   For Rakhmanov's density let $f$ be the cosine of the tail phase and $V$ the logarithmic potential. The potential is continuous on $[-1,1]$. The phase zeros there form a set $Y$ of $N-k$ points, all strictly inside the support. There is a positive continuous $g$ on $[-1,1]$ such that
--   $$\prod_{y\in Y}(z-y)=g(z)f(z).$$
--   This qualitative real-variable statement includes the removable values of the quotient at the simple zeros.
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, §2.1 (2.10)–(2.13), §3.1 (3.3)–(3.6), https://annals.math.princeton.edu/2007/165-1/p03

import Mathlib

theorem MomentSearch.rakhmanov_quantile_real_regularization (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    let V : ℝ → ℝ := fun z => ∫ t in (-1 : ℝ)..1, Real.log (1 / |z-t|) * ρ t
    ContinuousOn V (Set.Icc (-1 : ℝ) 1) ∧
    ∃ Y : Finset ℝ, Y.card = N-k ∧ (∀ y ∈ Y, y ∈ Set.Ioo (-r) r) ∧
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, z ∈ Y ↔ f z = 0) ∧
      ∃ g : ℝ → ℝ, ContinuousOn g (Set.Icc (-1 : ℝ) 1) ∧
        ∀ z ∈ Set.Icc (-1 : ℝ) 1, 0 < g z ∧
          (∏ y ∈ Y, (z-y)) = g z * f z := by sorry
