-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_triangle_side_bounds
-- name    : MomentSearch.rakhmanov_triangle_side_bounds
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-20T23:58:07.186244+00:00
-- url     : https://prove2.me/theorems/27960489-2aa2-4fa9-b0c6-c1cadc0c0cd3
-- title:
--   Bounds on the right side of the equilibrium triangle contour
-- statement:
--   On the right side $Z(t)=r(1-e^{-i\pi/3}t)$ of the equilateral contour, put $B(t)=2i\phi(Z(t))$ and $\eta(x)=\pi^{-1}\Im\int_0^2\log(1+e^{-B(t)})Z'(t)/(x-Z(t))\,dt$. With $D=2/(9e)+4/(3\pi\sqrt3)$, the one-sided bounds on $[-1,1]$ are
--   $$-\tfrac23\log2-D\le\eta(x)\le D\quad(x<r),\qquad -D\le\eta(x)\le\tfrac13\log2+D\quad(x>r).$$
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, §3.3, (3.26)–(3.31), https://annals.math.princeton.edu/2007/165-1/p03

import Mathlib

theorem MomentSearch.rakhmanov_triangle_side_bounds (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let s : ℂ := ⟨1/2, -Real.sqrt 3 / 2⟩
    let Z : ℝ → ℂ := fun t => (r : ℂ) * (1 - s * t)
    let B : ℝ → ℂ := fun t => 2 * Complex.I * (N : ℂ) * r * s *
      ∫ v in (0 : ℝ)..t, Complex.arctan ((N : ℂ) / k *
        (((r : ℂ)^2 - (Z v)^2) ^ (1/2 : ℂ)))
    let η : ℝ → ℝ := fun x => (∫ t in (0 : ℝ)..2,
      Complex.log (1 + Complex.exp (-(B t))) * (-(r : ℂ) * s) / ((x : ℂ) - Z t)).im / Real.pi
    let D := 2 / (9 * Real.exp 1) + 4 / (3 * Real.pi * Real.sqrt 3)
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      (z < r → -(2/3) * Real.log 2 - D ≤ η z ∧ η z ≤ D) ∧
      (r < z → -D ≤ η z ∧ η z ≤ (1/3) * Real.log 2 + D) := by sorry
