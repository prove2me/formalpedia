-- Prove2me | Theorems.Thm_KLTNuclear_Lasso_noise_sup_bound
-- name    : KLTNuclear.Lasso.noise_sup_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:30.041094+00:00
-- url     : https://prove2.me/theorems/5e4c5679-43eb-4ecc-b83b-2865e01ba6a9
-- title:
--   Proof of Theorem 14, p. 25 — ‖M‖∞ ≤ bσ√(2 log p/n) with probability at least 1 − 1/(p^{b²−1}√(π log p))
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^p$ be a fixed design with $n\ge1$, $p\ge2$, and suppose the diagonal elements of $\frac1n\mathbb X^\top\mathbb X$ are not larger than $1$. Let $\xi_1,\dots,\xi_n$ be i.i.d. $\mathcal N(0,\sigma^2)$ with $\sigma>0$, and let $b\ge1$. Then, with probability at least
--   $$
--   1-\frac{1}{p^{b^2-1}\sqrt{\pi\log p}},
--   $$
--   we have
--   $$
--   \|\mathbf M\|_\infty = \Big|\frac1n\sum_{i=1}^n\xi_ix_i\Big|_\infty \le b\sigma\sqrt{\frac{2\log p}{n}} .
--   $$
--
--   Combined with the deterministic Theorem 2 for the Lasso, this is what turns the condition $\lambda\ge3\|\mathbf M\|_\infty$ into the choice $\lambda = 3b\sqrt2\,\sigma\sqrt{\log p/n}$ of Theorem 14.
--
--   **Formalization Note** The statement bounds the probability of the complement, $P(\exists j: |\mathbf M(j)| > b\sigma\sqrt{2\log p/n}) \le 1/(p^{b^2-1}\sqrt{\pi\log p})$, with $\log$ the natural logarithm and $p^{b^2-1}$ a real power. The page has no explicit $p\ge2$; it is needed because for $p = 1$, $\log p = 0$ and the printed bound degenerates (division by $0$). $\sigma>0$ is the nondegenerate reading of $\mathcal N(0,\sigma^2)$. Independence is `iIndepFun`, each law is `gaussianReal 0 σ²`, and the noise variables are measurable.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 25, proof of Theorem 14, display ‖M‖∞ = |n⁻¹Σξ_ix_i|_∞ ≤ bσ√(2 log p/n)

import Mathlib
import Definitions.Def_KLTNuclear_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace KLTNuclear.Lasso

/-- Proof of Theorem 14, arXiv:1011.6256v4, p. 25. Fixed design `x₁, …, xₙ ∈ ℝ^p` with
`n ≥ 1`, `p ≥ 2` and the diagonal elements of `(1/n)𝕏ᵀ𝕏` at most `1`; noise `ξ_i` i.i.d.
`𝒩(0, σ²)` with `σ > 0`; `b ≥ 1`. Then, with probability at least
`1 − 1/(p^{b²−1} √(π log p))`,
`‖M‖∞ = |(1/n) ∑_i ξ_i x_i|_∞ ≤ b σ √(2 log p / n)`.
Formalization Note: the event `|v|_∞ ≤ t` is written `∀ j, |v(j)| ≤ t`; the statement bounds the
measure of the complement. -/
theorem noise_sup_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n p : ℕ} (hn : 0 < n) (hp : 2 ≤ p) (x : Fin n → Fin p → ℝ) (hx : GramDiagLeOne x)
    {σ : ℝ} (hσ : 0 < σ) {ξ : Fin n → Ω → ℝ} (hξ : IsGaussianNoise P ξ σ)
    {b : ℝ} (hb : 1 ≤ b) :
    P {ω | ¬ ∀ j : Fin p,
        |noiseVec x (fun i => ξ i ω) j| ≤ b * σ * Real.sqrt (2 * Real.log p / n)} ≤
      ENNReal.ofReal (1 / ((p : ℝ) ^ (b ^ 2 - 1) * Real.sqrt (Real.pi * Real.log p))) := by sorry

end KLTNuclear.Lasso
