-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_equilibrium_product_envelope
-- name    : MomentSearch.rakhmanov_equilibrium_product_envelope
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-20T23:37:30.091187+00:00
-- url     : https://prove2.me/theorems/b1990862-db66-4542-a003-5dfdecdc701e
-- title:
--   Weighted envelope for the equilibrium quantile polynomial
-- statement:
--   For $1\le k<N$, let $\rho$ be Rakhmanov's equilibrium density supported on $[-r,r]$, $r=\sqrt{1-k^2/N^2}$, and $f(z)=\cos(\pi\int_z^1\rho)$. Use the uniform-grid weight $w(z)=\exp(-N[(1+z)\log(1+z)+(1-z)\log(1-z)]/2)$. There exist a polynomial $S$ of degree at most $N-k$ and a positive amplitude $a$ on $[-1,1]$ such that
--   $$|S(z)|w(z)=a(z)|f(z)|,\qquad a(z)\le12a(x)\quad(|z|\le1,\ |x|<r).$$
--   At every interior phase zero $y$, the corresponding identity is $|S'(y)|w(y)=a(y)\pi\rho(y)$. This statement controls the full equilibrium product before removal of a selected root.
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, Annals of Mathematics 165 (2007), §2.1–2.2, https://annals.math.princeton.edu/2007/165-1/p03

import Mathlib

theorem MomentSearch.rakhmanov_equilibrium_product_envelope (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    let w : ℝ → ℝ := fun z => Real.exp (-(N : ℝ) / 2 *
      ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)))
    ∃ S : Polynomial ℝ, ∃ a : ℝ → ℝ,
      S.natDegree ≤ N-k ∧
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, 0 < a z ∧ |S.eval z| * w z = a z * |f z|) ∧
      (∀ x ∈ Set.Ioo (-r) r, ∀ z ∈ Set.Icc (-1 : ℝ) 1, a z ≤ 12 * a x) ∧
      (∀ y ∈ Set.Ioo (-r) r, f y = 0 →
        |S.derivative.eval y| * w y = a y * (Real.pi * ρ y)) := by sorry
