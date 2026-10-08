-- Prove2me | Theorems.Thm_FriendlyShadow_Gaussian_lemma_41
-- name    : FriendlyShadow.Gaussian.lemma_41
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:53:31.571896+00:00
-- url     : https://prove2.me/theorems/e25bbf22-0dda-458d-b1a3-2d600feeb4aa
-- title:
--   Lemma 41, p. 31 — height of simplex bound: E[|Σ zᵢhᵢ| | θ, t, S, x] ≥ τ/(2√d)
-- statement:
--   Let $d\ge3$, let $z\in\mathbb R^d$ with $\|z\|_1=1$, and let $\nu_1,\dots,\nu_d$ be probability densities on $\mathbb R$ with finite second moments and variances at least $\tau^2$, $\tau\ge0$. Let $h=(h_1,\dots,h_d)$ have joint density proportional to $|\sum_i z_ih_i|\prod_i\nu_i(h_i)$ (the conditional law of the heights in Lemma 37, with $\nu_i$ the restriction of $\bar\mu_i$ to the line $x+s_i+\mathbb R\bar\omega$). Then
--   $$\mathbb E\Big[\Big|\sum_{i=1}^d z_ih_i\Big|\Big]\ \ge\ \frac{\tau}{2\sqrt d},$$
--   stated multiplied out as
--   $$\frac{\tau}{2\sqrt d}\int\Big|\sum_i z_ih_i\Big|\prod_i\nu_i(h_i)\,dh\ \le\ \int\Big(\sum_i z_ih_i\Big)^2\prod_i\nu_i(h_i)\,dh .$$
--   Since the bound is uniform in the densities, it also bounds the infimum over the projected shift $x$, as on the page.
--
--   **Formalization Note** The page conditions on $(\theta,t,S,x)$ after Blaschke's change of variables. Here the conditioning is replaced by the explicit density that the page derives in Lemma 37 (p. 28) and uses in the proof (p. 31). The kernel combination $z(S)$ enters only through $\|z\|_1=1$, which is all the proof uses, so $z$ is any vector with $\|z\|_1=1$. Finite second moments are assumed: a density with infinite variance makes the page's expectation infinite and the bound trivial. Integrals are lower Lebesgue integrals in $[0,\infty]$.
-- source:
--   Dadush & Huiberts, arXiv:1711.05667v4, Lemma 41 and its proof, p. 31; density of Lemma 37, p. 28

import Mathlib

open MeasureTheory

namespace FriendlyShadow.Gaussian

/-- Lemma 41 (p. 31), on the explicit density of Lemma 37. Let `z ∈ ℝᵈ` with `‖z‖₁ = 1` and let
`ν₁, …, ν_d` be probability densities on `ℝ` with finite second moments and variances at least
`τ²`. If `h = (h₁, …, h_d)` has density proportional to `|Σ zᵢhᵢ| · Π νᵢ(hᵢ)`, then
`E[|Σ zᵢhᵢ|] ≥ τ/(2√d)`; cross-multiplied:
`τ/(2√d) · ∫ |Σ zᵢhᵢ| Π νᵢ(hᵢ) dh ≤ ∫ (Σ zᵢhᵢ)² Π νᵢ(hᵢ) dh`. -/
theorem lemma_41 {d : ℕ} (hd : 3 ≤ d) (z : Fin d → ℝ) (hz : ∑ i, |z i| = 1)
    (ν : Fin d → ℝ → ℝ) (hν0 : ∀ i γ, 0 ≤ ν i γ) (hνint : ∀ i, Integrable (ν i))
    (hν1 : ∀ i, ∫ γ, ν i γ = 1) (hν2 : ∀ i, Integrable (fun γ => γ ^ 2 * ν i γ))
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hvar : ∀ i, τ ^ 2 ≤ (∫ γ, γ ^ 2 * ν i γ) - (∫ γ, γ * ν i γ) ^ 2) :
    ENNReal.ofReal (τ / (2 * Real.sqrt d)) *
        ∫⁻ h : Fin d → ℝ, ENNReal.ofReal (|∑ i, z i * h i| * ∏ i, ν i (h i)) ≤
      ∫⁻ h : Fin d → ℝ, ENNReal.ofReal ((∑ i, z i * h i) ^ 2 * ∏ i, ν i (h i)) := by sorry

end FriendlyShadow.Gaussian
