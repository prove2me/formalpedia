-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_lower_half_plane_deformation
-- name    : MomentSearch.rakhmanov_lower_half_plane_deformation
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-21T00:17:28.289851+00:00
-- url     : https://prove2.me/theorems/b689f92c-fd13-4f0e-9fd3-7ffe772a5cd8
-- title:
--   Lower-half-plane deformation of the quantile discrepancy
-- statement:
--   Evaluate the two oriented upper triangle sides at $w=x-ih$, $h>0$, and write $E(x,h)$ for the imaginary part of the right-side transform divided by $\pi$. Reflection uses $-x-ih$ on the same side. For the interior quantiles $Y$, the cosine phase $f$, and $x$ off the nodes and support endpoints,
--   $$\sum_{y\in Y}\log|w-y|-\int_{-1}^1\log|w-t|\rho(t)\,dt=E(x,h)+E(-x,h)+\frac1\pi\int_{-r}^r\frac{h\log(2|f(t)|)}{(x-t)^2+h^2}\,dt.$$
--   The numerator of the right-side transform is interval integrable. All Cauchy denominators are separated from the lower-half-plane pole.
-- source:
--   Boundary-value decomposition of E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, §3.1, Th. 2 and (3.6), (3.9)–(3.11), https://annals.math.princeton.edu/2007/165-1/p03

import Mathlib

theorem MomentSearch.rakhmanov_lower_half_plane_deformation (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
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
    let L : ℝ → ℝ → ℝ := fun v h => Real.log ‖(v : ℂ) - (h : ℂ)*Complex.I‖
    let P : ℝ → ℝ → ℝ := fun x h => (∫ t in (-r)..r,
      h / ((x-t)^2+h^2) * Real.log (2*|f t|)) / Real.pi
    IntervalIntegrable (fun t : ℝ => Complex.log (1 + Complex.exp (-(B t))) * (-(r : ℂ) * s))
      MeasureTheory.volume 0 2 ∧
    ∀ Y : Finset ℝ, Y.card = N-k → (∀ y ∈ Y, y ∈ Set.Ioo (-r) r) →
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, z ∈ Y ↔ f z = 0) →
      ∀ z ∈ Set.Icc (-1 : ℝ) 1, z ∉ Y → z ≠ r → z ≠ -r →
        ∀ h : ℝ, 0 < h →
          (∑ y ∈ Y, L (z-y) h) - (∫ t in (-1 : ℝ)..1, L (z-t) h * ρ t) =
            P z h + E z h + E (-z) h := by sorry
