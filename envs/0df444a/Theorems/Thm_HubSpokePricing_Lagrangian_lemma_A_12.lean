-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_lemma_A_12
-- name    : HubSpokePricing.Lagrangian.lemma_A_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:35.020801+00:00
-- url     : https://prove2.me/theorems/7e866f6b-3b27-4cb9-bb5a-af968f081c74
-- title:
--   Lemma A.12, p. 52 — tail bound (42) for a sum of independent discrete log-concave variables with means at most c
-- statement:
--   Let $X_1,\dots,X_n$ be independent random variables on $\{0,1,2,\dots\}$, each with a discrete log-concave law (Definition B.1) and mean $\mu_i=\mathbb E[X_i]$. Suppose $\mu_i\le c$ for all $i\in[n]$, for a constant $c>0$. Let $X=\sum_{i=1}^nX_i$ and $\mu=\mathbb E[X]=\sum_{i=1}^n\mu_i$. Then for every $\lambda\ge1$,
--   $$\mathbb P[X\ge\lambda\mu]\;\le\;\exp\Big\{-\frac{(\lambda-1)\mu}{1+c}-\frac{n+\mu}{1+c}\,\ln\Big(1-\frac{\lambda\mu-\mu}{\lambda\mu+n}\Big)\Big\}.\qquad(42)$$
--
--   This is a Chernoff-type concentration inequality for sums of independent log-concave variables with uniformly bounded means, extending Janson's bound for sums of geometric variables; with $\lambda\mu=m$ it bounds the relaxed hub's depletion probability (Proposition 4.6).
--
--   **Formalization Note** The law of $X$ is the iterated convolution of the laws of the $X_i$ (independence as product form). The paper writes "for all $i\le[n]$", read as $i\in[n]$. No positivity of $\mu$ is assumed: at $\mu=0$ both sides equal $1$.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, p. 52, Lemma A.12, (42)

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Prob

namespace HubSpokePricing.Lagrangian

/-- Lemma A.12 (p. 52): for independent discrete log-concave `X₁, …, Xₙ` with means `μᵢ ≤ c`,
`c > 0`, `X = ∑ᵢ Xᵢ`, `μ = ∑ᵢ μᵢ` and `λ ≥ 1`,
`ℙ[X ≥ λμ] ≤ exp(−(λ − 1)μ/(1 + c) − ((n + μ)/(1 + c)) ln(1 − (λμ − μ)/(λμ + n)))`, (42). -/
theorem lemma_A_12 (n : ℕ) (ps : Fin n → ℕ → ℝ) (hlc : ∀ i, IsLogConcave (ps i))
    (c : ℝ) (hc : 0 < c) (hmean : ∀ i, pmfMean (ps i) ≤ c) (lam : ℝ) (hlam : 1 ≤ lam) :
    ∑' k : ℕ, (if lam * (∑ i, pmfMean (ps i)) ≤ (k : ℝ) then sumLaw n ps k else 0) ≤
      Real.exp (-((lam - 1) * (∑ i, pmfMean (ps i))) / (1 + c) -
        ((n : ℝ) + ∑ i, pmfMean (ps i)) / (1 + c) *
          Real.log (1 - (lam * (∑ i, pmfMean (ps i)) - ∑ i, pmfMean (ps i)) /
            (lam * (∑ i, pmfMean (ps i)) + n))) := by sorry

end HubSpokePricing.Lagrangian
