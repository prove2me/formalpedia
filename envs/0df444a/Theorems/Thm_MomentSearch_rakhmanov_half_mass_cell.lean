-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_half_mass_cell
-- name    : MomentSearch.rakhmanov_half_mass_cell
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-20T23:42:13.303433+00:00
-- url     : https://prove2.me/theorems/26bb6d77-fd9e-471f-acd1-e2ec542e5af0
-- title:
--   Half-mass cell for the Rakhmanov equilibrium density
-- statement:
--   For the equilibrium density $\rho$ on $[-r,r]$, each interior $x$ belongs to a unit-mass interval $[a,b]$ with median $y$ at a half-integer tail mass. Specifically, the masses of $[a,y]$ and $[y,b]$ are both $1/2$. The density is concave on the cell, and there is a point $p$ such that
--   $$\rho(z)\le\rho(p)\le 2\rho(y)\qquad(a\le z\le b).$$
--   The cell thus controls local density using only its median and its mass.
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, Annals of Mathematics 165 (2007), §2.1–2.2, https://annals.math.princeton.edu/2007/165-1/p03

import Mathlib

theorem MomentSearch.rakhmanov_half_mass_cell (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    ∀ x ∈ Set.Ioo (-r) r, ∃ a b y p : ℝ, ∃ m : ℤ,
      y ∈ Set.Ioo (-r) r ∧ y ∈ Set.Icc a b ∧ x ∈ Set.Icc a b ∧
      (∫ t in y..1, ρ t) = (m : ℝ) + 1/2 ∧
      (∫ t in a..y, ρ t) = 1/2 ∧ (∫ t in y..b, ρ t) = 1/2 ∧
      ConcaveOn ℝ (Set.Icc a b) ρ ∧
      (∀ z ∈ Set.Icc a b, ρ z ≤ ρ p) ∧ ρ p ≤ 2 * ρ y := by sorry
