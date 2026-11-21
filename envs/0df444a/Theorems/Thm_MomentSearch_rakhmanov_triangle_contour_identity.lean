-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_triangle_contour_identity
-- name    : MomentSearch.rakhmanov_triangle_contour_identity
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-20T23:58:07.657005+00:00
-- url     : https://prove2.me/theorems/d8adf81f-a063-4dd9-9174-5c34402959da
-- title:
--   Equilateral contour identity for the quantile polynomial
-- statement:
--   Let $Z(t)=r(1-e^{-i\pi/3}t)$ for $0\le t\le2$, let $B(t)=2i\phi(Z(t))$ be obtained by integrating the equilibrium density along this side from $Z(t)$ back to $r$, and let $\eta(x)=\pi^{-1}\Im\int_0^2\log(1+e^{-B(t)})Z'(t)/(x-Z(t))\,dt$. For the real phase cosine $f$ and logarithmic potential $V$, there is a polynomial $S$ of degree at most $N-k$ with $S=e^{H-V}f$ on $[-1,1]$. Its log amplitude $H$ is continuous there, and off the two support endpoints
--   $$H(x)=\mathbf{1}_{|x|<r}\log2+\eta(x)+\eta(-x).$$
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, Theorem 2 and (3.11), (3.14), (3.23), (3.32)–(3.34), https://annals.math.princeton.edu/2007/165-1/p03

import Mathlib

theorem MomentSearch.rakhmanov_triangle_contour_identity (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    let V : ℝ → ℝ := fun z => ∫ t in (-1 : ℝ)..1, Real.log (1 / |z-t|) * ρ t
    let s : ℂ := ⟨1/2, -Real.sqrt 3 / 2⟩
    let Z : ℝ → ℂ := fun t => (r : ℂ) * (1 - s * t)
    let B : ℝ → ℂ := fun t => 2 * Complex.I * (N : ℂ) * r * s *
      ∫ v in (0 : ℝ)..t, Complex.arctan ((N : ℂ) / k *
        (((r : ℂ)^2 - (Z v)^2) ^ (1/2 : ℂ)))
    let η : ℝ → ℝ := fun x => (∫ t in (0 : ℝ)..2,
      Complex.log (1 + Complex.exp (-(B t))) * (-(r : ℂ) * s) / ((x : ℂ) - Z t)).im / Real.pi
    ∃ S : Polynomial ℝ, ∃ H : ℝ → ℝ, S.natDegree ≤ N-k ∧
      ContinuousOn H (Set.Icc (-1 : ℝ) 1) ∧
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, S.eval z = Real.exp (H z) * Real.exp (-V z) * f z) ∧
      ∀ z ∈ Set.Icc (-1 : ℝ) 1, z ≠ r → z ≠ -r →
        H z = (if |z| < r then Real.log 2 else 0) + η z + η (-z) := by sorry
