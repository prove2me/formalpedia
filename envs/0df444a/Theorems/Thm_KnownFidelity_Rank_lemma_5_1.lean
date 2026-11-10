-- Prove2me | Theorems.Thm_KnownFidelity_Rank_lemma_5_1
-- name    : KnownFidelity.Rank.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:47.801095+00:00
-- url     : https://prove2.me/theorems/2372eea1-3a70-4a22-bc69-294e16ca9d63
-- title:
--   Lemma 5.1 — Gaussian concentration $\mathbb P[f(X)\le\mathbb Ef(X)-t]\le\exp(-ct^2/L^2)$, real and complex
-- statement:
--   There is a universal constant $c>0$ such that the following holds. Let $X$ be a standard Gaussian vector in a finite-dimensional real or complex Euclidean space: $X\sim N(0,I_n)$ on $\mathbb R^n$, or $X$ on $\mathbb C^n$ with independent coordinates whose real and imaginary parts are independent $N(0,1/2)$. If $f$ is $L$-Lipschitz for the Euclidean distance, then for every $t\ge0$
--
--   $$\mathbb P\big[f(X)\le\mathbb Ef(X)-t\big]\ \le\ \exp\Big(-c\,\frac{t^2}{L^2}\Big).$$
--
--   This form of Gaussian isoperimetry is used for the nuclear norm of a Ginibre matrix (Lemma 5.13).
--
--   **Formalization Note** $\mathbb R^n$ and $\mathbb C^n$ are `Fin n → ℝ` and `Fin n → ℂ`, with the product of `gaussianReal 0 1` and of the platform's `BraneBrauer.Orthogonal.complexGaussian` respectively; the Lipschitz condition is written with the Euclidean distance.
--
--   Differences from the source:
--   - encoding: f is L-Lipschitz (L ≥ 0 implicit) → L > 0; reason: at L = 0 the printed bound t²/L² is undefined; f is then constant
--   - encoding: a finite-dimensional real or complex Euclidean space → Fin n → ℝ and Fin n → ℂ with the Lipschitz condition in the Euclidean distance √(Σ|x_i − y_i|²); reason: every finite-dimensional Euclidean space is isometric to one of these with the standard Gaussian preserved
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §5.2 and Lemma 5.1, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_BraneBrauer_Orthogonal_ComplexGaussian

open MeasureTheory

namespace KnownFidelity.Rank

/-- **Lemma 5.1 (Gaussian concentration).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §5.2 and Lemma 5.1, printed p. 12 (PDF p. 14): "We use the following form of Gaussian
isoperimetry [8], stated with a universal constant to cover standard complex Gaussians whose real
and imaginary parts have variance 1/2. Lemma 5.1 (Gaussian concentration). Let X be a standard
Gaussian vector in a finite-dimensional real or complex Euclidean space. If f is L-Lipschitz, then
for every t ≥ 0, P[f(X) ≤ Ef(X) − t] ≤ exp(−c t²/L²) (26) for a universal constant c > 0."

One universal `c > 0` serves both cases, every dimension `n`, every `L > 0` and every `t ≥ 0`:
(real) `X ∼ N(0, I_n)` on `ℝ^n`; (complex) `X` on `ℂ^n` with independent coordinates whose real and
imaginary parts are independent `N(0, 1/2)`. In each case `f` is `L`-Lipschitz for the Euclidean
distance.

**Formalization Note.** `ℝ^n` is `Fin n → ℝ` with the product of `gaussianReal 0 1`; `ℂ^n` is
`Fin n → ℂ` with the product of the platform's `BraneBrauer.Orthogonal.complexGaussian`. The Lipschitz condition is written
with the Euclidean distance `√(Σ |x_i − y_i|²)` (not Lean's sup norm on `Fin n → ℝ`). `L > 0`
excludes the constant case, where the printed `t²/L²` is undefined. A Lipschitz `f` is integrable
under a Gaussian, so `E f(X)` is a genuine Bochner integral. -/
theorem lemma_5_1 :
    ∃ c : ℝ, 0 < c ∧
      (∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ), 0 < L →
        (∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) →
        ∀ t : ℝ, 0 ≤ t →
          (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)
              {x | f x ≤ (∫ y, f y ∂(Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)) - t} ≤
            ENNReal.ofReal (Real.exp (-c * t ^ 2 / L ^ 2))) ∧
      (∀ (n : ℕ) (f : (Fin n → ℂ) → ℝ) (L : ℝ), 0 < L →
        (∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, ‖x i - y i‖ ^ 2)) →
        ∀ t : ℝ, 0 ≤ t →
          (Measure.pi fun _ : Fin n => BraneBrauer.Orthogonal.complexGaussian)
              {x | f x ≤ (∫ y, f y ∂(Measure.pi fun _ : Fin n => BraneBrauer.Orthogonal.complexGaussian)) - t} ≤
            ENNReal.ofReal (Real.exp (-c * t ^ 2 / L ^ 2))) := by sorry

end KnownFidelity.Rank
