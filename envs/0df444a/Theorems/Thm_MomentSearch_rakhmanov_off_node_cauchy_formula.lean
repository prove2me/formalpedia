-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_off_node_cauchy_formula
-- name    : MomentSearch.rakhmanov_off_node_cauchy_formula
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-21T00:03:06.777772+00:00
-- url     : https://prove2.me/theorems/1b29edb0-108b-4611-83e6-55f06b49e122
-- title:
--   Off-node logarithmic Cauchy formula on the equilibrium triangle
-- statement:
--   Let $Y$ be the $N-k$ interior midpoint quantiles, $f$ the cosine phase, $V$ the logarithmic potential, and $\eta$ the imaginary part of the right-side Cauchy integral divided by $\pi$. For $z\in[-1,1]\setminus(Y\cup\{-r,r\})$,
--   $$\sum_{y\in Y}\log|z-y|+V(z)-\log|f(z)|=\mathbf1_{|z|<r}\log2+\eta(z)+\eta(-z).$$
--   The right-side numerator $\log(1+e^{-B(t)})Z'(t)$ is integrable on its finite parameter interval. The formula concerns ordinary logarithms off the nodes.
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, Theorem 2, (3.6), (3.10)–(3.11), (3.14), (3.23), https://annals.math.princeton.edu/2007/165-1/p03

import Mathlib

theorem MomentSearch.rakhmanov_off_node_cauchy_formula (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
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
    IntervalIntegrable (fun t : ℝ => Complex.log (1 + Complex.exp (-(B t))) * (-(r : ℂ) * s))
      MeasureTheory.volume 0 2 ∧
    ∀ Y : Finset ℝ, Y.card = N-k → (∀ y ∈ Y, y ∈ Set.Ioo (-r) r) →
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, z ∈ Y ↔ f z = 0) →
      ∀ z ∈ Set.Icc (-1 : ℝ) 1, z ∉ Y → z ≠ r → z ≠ -r →
        (∑ y ∈ Y, Real.log |z-y|) + V z - Real.log |f z| =
          (if |z| < r then Real.log 2 else 0) + η z + η (-z) := by sorry
