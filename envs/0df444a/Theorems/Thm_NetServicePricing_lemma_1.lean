-- Prove2me | Theorems.Thm_NetServicePricing_lemma_1
-- name    : NetServicePricing.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:39:34.416996+00:00
-- url     : https://prove2.me/theorems/9e9d9aa0-8090-4021-8fdd-7dc4eb9a593c
-- title:
--   Lemma 1 — closed form of the fixed-price revenue $\Gamma(x;p)$
-- statement:
--   Let $M$ be a network on $n$ consumers, $\mu\in[0,1]$ the habit coefficient, $\delta\in(0,1)$ the discount factor and $\alpha,\beta>0$, and assume Assumption 1. Let $v_1,\dots,v_n$ be an orthonormal eigenbasis of $M$ with eigenvalues $\lambda_1,\dots,\lambda_n$; the same vectors are eigenvectors of $\widehat M=M+\mu I_n$ with eigenvalues $\hat\lambda_i=\lambda_i+\mu$. Write $\langle v_i,\mathbf 1\rangle=\sum_j v_{ij}$.
--
--   For every price $p\le\alpha/\beta$ and every initial consumption vector $x\in\mathbb R^n$, the series defining $\Gamma(x;p)$ converges and
--
--   $$\Gamma(x;p)=\sum_{i=1}^{n}\frac{p(\alpha-\beta p)\delta\langle v_i,\mathbf 1\rangle^2+p\delta(1-\delta)\hat\lambda_i\langle v_i,\mathbf 1\rangle\langle v_i,x\rangle}{(1-\delta)(1-\delta\hat\lambda_i)}.$$
--
--   The revenue thus splits into $n$ decoupled parts, one for each eigenpair of $\widehat M$. Under Assumption 1, $1-\delta\hat\lambda_i>0$, so no denominator vanishes.
--
--   Differences from the source:
--   - generalization: v_i, λ̂_i the eigenvectors and eigenvalues of M̂ → any orthonormal eigenbasis v of M with eigenvalues lam, and λ̂_i = lam i + μ; reason: an eigenbasis of M is exactly an eigenbasis of M̂ = M + μI with eigenvalues shifted by μ (Fact 3); the paper fixes one unspecified eigenbasis, and the statement for every one specializes to it
--   - generalization: initial consumption vector x → any x ∈ ℝⁿ; reason: the closed form holds for every real vector; consumption vectors are a special case
--   - reading: α, β constant coefficients → 0 < α, 0 < β; reason: the quadratic term of (1) has the negative sign to induce concavity, which needs β > 0, and the price cap α/β with nonnegative prices needs α ≥ 0; standing assumption of every statement
--   - encoding: periods t = 1, 2, … and consumers 1, …, n → the sum over t ∈ ℕ of the term for period t + 1, and consumers Fin n; reason: reindexing only
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, Lemma 1, p.13

import Mathlib
import Definitions.Def_NetServicePricing_IsNetwork
import Definitions.Def_NetServicePricing_Assumption1
import Definitions.Def_NetServicePricing_fixedPriceTraj
import Definitions.Def_NetServicePricing_fixedPriceRevenue

open Matrix

namespace NetServicePricing

/-- **Lemma 1 (closed form of the fixed-price revenue).**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, Lemma 1, p.13: "For any given price p ≤ α/β and initial consumption vector x,
Γ(x;p) = ∑_{i=1}^n [p(α − βp)δ⟨vi,1⟩² + pδ(1 − δ)λ̂i⟨vi,1⟩⟨vi,x⟩] / [(1 − δ)(1 − δλ̂i)]",
where "λ̂i and vi are the ith eigenvalue and eigenvector of matrix M̂" (p.12).

Under the standing assumptions (a network `M`, `μ ∈ [0,1]`, `δ ∈ (0,1)`, `α, β > 0`,
Assumption 1), the series defining `Γ(x;p)` converges and its sum is the closed form.

**Formalization Note** `v` is an arbitrary orthonormal eigenbasis of `M` with eigenvalues `lam`;
it is an eigenbasis of `M̂ = M + μI` with eigenvalues `λ̂ᵢ = lam i + μ` (Fact 3, p.ec2), and
conversely. `⟨vᵢ, 𝟏⟩ = ∑ⱼ vᵢⱼ`, `⟨vᵢ, x⟩ = ∑ⱼ vᵢⱼ xⱼ`. The initial vector `x` is any real vector.
Time is shifted to `ℕ` (`t + 1` is the paper's `t`). -/
theorem lemma_1 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (μ δ α β : ℝ)
    (hM : IsNetwork M) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hα : 0 < α) (hβ : 0 < β) (hA : Assumption1 M μ δ)
    (v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (lam : Fin n → ℝ)
    (hv : ∀ i, M *ᵥ ⇑(v i) = lam i • ⇑(v i))
    (p : ℝ) (hp : p ≤ α / β) (x : Fin n → ℝ) :
    Summable (fun t : ℕ => δ ^ (t + 1) * p * ∑ j, fixedPriceTraj M μ α β p x (t + 1) j) ∧
    fixedPriceRevenue M μ α β δ p x =
      ∑ i, (p * (α - β * p) * δ * (∑ j, v i j) ^ 2 +
          p * δ * (1 - δ) * (lam i + μ) * (∑ j, v i j) * (∑ j, v i j * x j)) /
        ((1 - δ) * (1 - δ * (lam i + μ))) := by sorry

end NetServicePricing
