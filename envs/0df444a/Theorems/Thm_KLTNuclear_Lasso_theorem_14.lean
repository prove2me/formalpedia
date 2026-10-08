-- Prove2me | Theorems.Thm_KLTNuclear_Lasso_theorem_14
-- name    : KLTNuclear.Lasso.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:24.52321+00:00
-- url     : https://prove2.me/theorems/1e96d195-b093-48ba-b38e-2aae24e90af3
-- title:
--   Theorem 14 — with Gaussian noise and λ = 3b√2 σ√(log p/n), the Lasso satisfies the sharp sparsity oracle inequality (5.12)
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^p$ be fixed, with $n\ge1$, $p\ge2$, design matrix $\mathbb X = (x_1,\dots,x_n)^\top$, and suppose the diagonal elements of $\frac1n\mathbb X^\top\mathbb X$ are not larger than $1$. Observe
--   $$
--   Y_i = x_i^\top\beta^*+\xi_i,\qquad i=1,\dots,n,
--   $$
--   where $\beta^*\in\mathbb R^p$ and $\xi_1,\dots,\xi_n$ are i.i.d. $\mathcal N(0,\sigma^2)$, $\sigma>0$. Take
--   $$
--   \lambda = C\sigma\sqrt{\frac{\log p}{n}},\qquad C = 3b\sqrt2,\quad b\ge1,
--   $$
--   and let $\hat\beta^\lambda$ be any Lasso estimator, i.e. any minimizer of $\frac1n\sum_i(Y_i-x_i^\top\beta)^2+\lambda|\beta|_1$ over $\beta\in\mathbb R^p$. Then, with probability at least $1-\frac{1}{p^{b^2-1}\sqrt{\pi\log p}}$,
--   $$
--   \frac1n|\mathbb X(\hat\beta^\lambda-\beta^*)|_2^2 \le \inf_{\beta\in\mathbb R^p}\Big\{\frac1n|\mathbb X(\beta-\beta^*)|_2^2 + C^2\sigma^2\frac{\mu^2(\beta)M(\beta)\log p}{n}\Big\},
--   $$
--   where $M(\beta)$ is the number of nonzero components of $\beta$ and $\mu(\beta) = \mu_5(\beta)$ is the restricted constant of $\beta$:
--   the infimum of the $\mu'>0$ such that $|u_J|_2\le\mu' n^{-1/2}|\mathbb Xu|_2$ for every $u$ with $|u_{J^c}|_1\le5|u_J|_1$, $J$ the support of $\beta$.
--
--   This is a sparsity oracle inequality with leading constant $1$: the Lasso predicts as well as the best trade-off between approximation error and sparsity, without the factor larger than one that appears in earlier oracle inequalities for the Lasso.
--
--   **Formalization Note** The event is uniform in $\beta$: the statement bounds the (outer) measure of the set of outcomes $\omega$ for which some $\beta$ and some witness $\mu'$ of $\mu(\beta)$ violate the bound, by $1/(p^{b^2-1}\sqrt{\pi\log p})$ (natural logarithm, real power). The infimum over $\beta$ is "for every $\beta$", and $\mu(\beta)$ enters through its witnesses, which is equivalent to the infimum since the bound is continuous and increasing in $\mu'$ (a real infimum over an empty set would be $0$ and is not used). $\hat\beta$ is a function of the outcome that is a Lasso minimizer at every outcome; no measurability is assumed. Added relative to the page: $p\ge2$ (for $p = 1$ the printed probability bound divides by $0$), $n \ge 1$, $\sigma>0$, and measurability of the $\xi_i$. The constant $C = 3b\sqrt2$ is kept unfolded, as printed.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 25, Theorem 14, (5.12); setting §5.4, pp. 24–25; μ_{c₀} p. 10

import Mathlib
import Definitions.Def_KLTNuclear_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace KLTNuclear.Lasso

/-- Theorem 14, (5.12), arXiv:1011.6256v4, p. 25: the sharp sparsity oracle inequality for the
Lasso with Gaussian noise. Fixed design `x₁, …, xₙ ∈ ℝ^p` with `n ≥ 1`, `p ≥ 2` and the diagonal
elements of `(1/n)𝕏ᵀ𝕏` at most `1`; `Y_i = x_iᵀβ* + ξ_i` with `ξ_i` i.i.d. `𝒩(0, σ²)`, `σ > 0`;
`λ = Cσ√(log p / n)` with `C = 3b√2`, `b ≥ 1`; `β̂(ω)` any Lasso minimizer for the data at `ω`.
Then, with probability at least `1 − 1/(p^{b²−1} √(π log p))`, simultaneously for all `β ∈ ℝ^p`,
`(1/n)|𝕏(β̂ − β*)|_2² ≤ (1/n)|𝕏(β − β*)|_2² + C²σ² μ²(β) M(β) log p / n`.
Formalization Note: the event is uniform in `β`; the statement bounds the (outer) measure of
the bad set `{ω | ∃ β, ∃ μ' witness of μ(β), the bound fails}`. `μ(β)` enters through its
witnesses (`IsMuWitness x 5 β μ'`), equivalent to the infimum since the bound is continuous and
increasing in `μ'`. -/
theorem theorem_14 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n p : ℕ} (hn : 0 < n) (hp : 2 ≤ p) (x : Fin n → Fin p → ℝ) (hx : GramDiagLeOne x)
    (βstar : Fin p → ℝ) {σ : ℝ} (hσ : 0 < σ) {ξ : Fin n → Ω → ℝ} (hξ : IsGaussianNoise P ξ σ)
    (Y : Fin n → Ω → ℝ) (hY : ∀ i ω, Y i ω = ∑ j, x i j * βstar j + ξ i ω)
    {b C lam : ℝ} (hb : 1 ≤ b) (hC : C = 3 * b * Real.sqrt 2)
    (hlam : lam = C * σ * Real.sqrt (Real.log p / n))
    (βhat : Ω → Fin p → ℝ) (hβhat : ∀ ω, IsLasso x (fun i => Y i ω) lam (βhat ω)) :
    P {ω | ∃ β : Fin p → ℝ, ∃ μ' : ℝ, IsMuWitness x 5 β μ' ∧
        ¬ (predLoss x (βhat ω) βstar ≤
            predLoss x β βstar + C ^ 2 * σ ^ 2 * (μ' ^ 2 * (sparsity β : ℝ) * Real.log p / n))} ≤
      ENNReal.ofReal (1 / ((p : ℝ) ^ (b ^ 2 - 1) * Real.sqrt (Real.pi * Real.log p))) := by sorry

end KLTNuclear.Lasso
