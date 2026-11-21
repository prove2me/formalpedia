-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_triangle_logarithm_trace
-- name    : MomentSearch.rakhmanov_triangle_logarithm_trace
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-21T00:24:43.196887+00:00
-- url     : https://prove2.me/theorems/408517b3-e152-4da6-aa0f-3f4391dbc121
-- title:
--   Boundary trace of the logarithmic phase on the triangle
-- statement:
--   Let $Y$ be the midpoint quantiles of the equilibrium density $\rho$ on $[-r,r]$. Put $D(t)=\#\{y\in Y:y\ge t\}-\int_t^r\rho(u)\,du$ and $f(t)=\cos(\pi\int_t^r\rho)$. For $w=x-ih$, $h>0$, let $E(x,h)$ denote the normalized imaginary part of the right-side Cauchy integral of the logarithmic phase, as in the finite-height deformation formula. Then
--   $$E(x,h)+E(-x,h)=\int_{-r}^r\frac{(t-x)D(t)-(h/\pi)\log(2|f(t)|)}{(x-t)^2+h^2}\,dt.$$
--   This is the imaginary part of the deformation of the two sloping sides to the real edge. The pole can be anywhere in the open lower half-plane.
-- source:
--   Boundary-value decomposition of E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, §3.1, Th. 2 and (3.6), (3.9)–(3.11), https://annals.math.princeton.edu/2007/165-1/p03

import Mathlib

theorem MomentSearch.rakhmanov_triangle_logarithm_trace (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    let s : ℂ := ⟨1/2, -Real.sqrt 3 / 2⟩
    let Z : ℝ → ℂ := fun t => (r : ℂ) * (1 - s * t)
    let B : ℝ → ℂ := fun t => 2 * Complex.I * (N : ℂ) * r * s *
      ∫ v in (0 : ℝ)..t, Complex.arctan ((N : ℂ) / k *
        (((r : ℂ)^2 - (Z v)^2) ^ (1/2 : ℂ)))
    let E : ℝ → ℝ → ℝ := fun x h => (∫ t in (0 : ℝ)..2,
      Complex.log (1 + Complex.exp (-(B t))) * (-(r : ℂ) * s) /
        ((x : ℂ) - (h : ℂ)*Complex.I - Z t)).im / Real.pi
    let P : ℝ → ℝ → ℝ := fun x h => (∫ t in (-r)..r,
      h / ((x-t)^2+h^2) * Real.log (2*|f t|)) / Real.pi
    ∀ Y : Finset ℝ, Y.card = N-k → (∀ y ∈ Y, y ∈ Set.Ioo (-r) r) →
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, z ∈ Y ↔ f z = 0) →
      ∀ x h : ℝ, 0 < h →
        (∫ t in (-r)..r,
          ((∑ y ∈ Y, if t ≤ y then (1 : ℝ) else 0) - (∫ u in t..r, ρ u)) *
            ((t-x)/((x-t)^2+h^2))) = P x h + E x h + E (-x) h := by sorry
