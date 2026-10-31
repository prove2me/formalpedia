-- Prove2me | Theorems.Thm_NetServicePricing_lemma_EC_1
-- name    : NetServicePricing.lemma_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:39:33.566138+00:00
-- url     : https://prove2.me/theorems/04897148-0980-4452-9c87-fb25e5f70de7
-- title:
--   Lemma EC.1 — closed form (EC.2) of the revenue $J(\mathbf 0;\tau,p)$ of a policy
-- statement:
--   Let $M$ be a network on $n$ consumers, $\mu\in[0,1]$ the habit coefficient, $\delta\in(0,1)$ the discount factor and $\alpha,\beta>0$, and assume Assumption 1. Let $v_1,\dots,v_n$ be an orthonormal eigenbasis of $M$ with eigenvalues $\lambda_1,\dots,\lambda_n$; the same vectors are eigenvectors of $\widehat M=M+\mu I_n$ with eigenvalues $\hat\lambda_i=\lambda_i+\mu$. Write $\langle v_i,\mathbf 1\rangle=\sum_j v_{ij}$.
--
--   For every policy $(\tau,p)$, i.e. $\tau\in\{0,1,2,\dots\}$ and $p\in[0,\alpha/\beta]$, the revenue series converges and
--
--   $$J(\mathbf 0;\tau,p)=\sum_{i=1}^{n}\frac{p(\alpha-\beta p)\delta^{\tau+1}\langle v_i,\mathbf 1\rangle^2}{(1-\delta)(1-\delta\hat\lambda_i)}+\alpha\sum_{i=1}^{n}\frac{\delta^{\tau+1}\hat\lambda_i\,p\,(1-\hat\lambda_i^{\tau})\langle v_i,\mathbf 1\rangle^2}{(1-\delta\hat\lambda_i)(1-\hat\lambda_i)}.$$
--
--   This expresses the revenue of any policy through the spectrum of $\widehat M$ and the projections of $\mathbf 1$ on its eigenvectors. Under Assumption 1, $1-\hat\lambda_i>0$ and $1-\delta\hat\lambda_i>0$.
--
--   Differences from the source:
--   - generalization: v_i, λ̂_i the eigenvectors and eigenvalues of M̂ → any orthonormal eigenbasis v of M with eigenvalues lam, and λ̂_i = lam i + μ; reason: an eigenbasis of M is exactly an eigenbasis of M̂ = M + μI with eigenvalues shifted by μ (Fact 3); the paper fixes one unspecified eigenbasis, and the statement for every one specializes to it
--   - reading: a given policy (τ,p) → τ ∈ ℕ and p ∈ [0, α/β]; reason: the policy class of the mission (see Policy)
--   - reading: α, β constant coefficients → 0 < α, 0 < β; reason: the quadratic term of (1) has the negative sign to induce concavity, which needs β > 0, and the price cap α/β with nonnegative prices needs α ≥ 0; standing assumption of every statement
--   - encoding: periods t = 1, 2, … and consumers 1, …, n → the sum over t ∈ ℕ of the term for period t + 1, and consumers Fin n; reason: reindexing only
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, Lemma EC.1, (EC.2), p.ec4

import Mathlib
import Definitions.Def_NetServicePricing_IsNetwork
import Definitions.Def_NetServicePricing_Assumption1
import Definitions.Def_NetServicePricing_consumption
import Definitions.Def_NetServicePricing_revenue

open Matrix

namespace NetServicePricing

/-- **Lemma EC.1 (closed form of the revenue of a policy `(τ, p)`).**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, Lemma EC.1, p.ec4: "Denote the total discounted revenue when the firm follows a given
policy (τ,p) by J(0;τ,p), starting from x0 = 0. … The revenue for a given policy (τ,p) is
J(0;τ,p) = ∑_{i=1}^n p(α − βp)δ^{τ+1}⟨vi,1⟩² / [(1 − δ)(1 − δλ̂i)]
+ α ∑_{i=1}^n δ^{τ+1}λ̂i p(1 − λ̂i^τ)⟨vi,1⟩² / [(1 − δλ̂i)(1 − λ̂i)]. (EC.2)"

Under the standing assumptions, for every policy `(τ, p)` (`τ ∈ ℕ`, `p ∈ [0, α/β]`) the series
(3) converges and its sum is (EC.2).

**Formalization Note** `v` is an arbitrary orthonormal eigenbasis of `M` with eigenvalues `lam`,
and `λ̂ᵢ = lam i + μ` are the eigenvalues of `M̂` for the same eigenvectors (Fact 3, p.ec2).
`⟨vᵢ, 𝟏⟩ = ∑ⱼ vᵢⱼ`. Under Assumption 1, `1 − λ̂ᵢ > 0` and `1 − δλ̂ᵢ > 0`, so no denominator
vanishes. -/
theorem lemma_EC_1 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (μ δ α β : ℝ)
    (hM : IsNetwork M) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hα : 0 < α) (hβ : 0 < β) (hA : Assumption1 M μ δ)
    (v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (lam : Fin n → ℝ)
    (hv : ∀ i, M *ᵥ ⇑(v i) = lam i • ⇑(v i))
    (τ : ℕ) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) (α / β)) :
    Summable (fun t : ℕ => δ ^ (τ + t + 1) * p * ∑ i, consumption M μ α β τ p (τ + t + 1) i) ∧
    revenue M μ α β δ τ p =
      (∑ i, p * (α - β * p) * δ ^ (τ + 1) * (∑ j, v i j) ^ 2 /
          ((1 - δ) * (1 - δ * (lam i + μ)))) +
        α * ∑ i, δ ^ (τ + 1) * (lam i + μ) * p * (1 - (lam i + μ) ^ τ) * (∑ j, v i j) ^ 2 /
          ((1 - δ * (lam i + μ)) * (1 - (lam i + μ))) := by sorry

end NetServicePricing
