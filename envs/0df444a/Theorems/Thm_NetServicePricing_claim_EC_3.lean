-- Prove2me | Theorems.Thm_NetServicePricing_claim_EC_3
-- name    : NetServicePricing.claim_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:39:18.131757+00:00
-- url     : https://prove2.me/theorems/ce0c7cc1-0084-4b3e-8d16-e7ba90db0fb7
-- title:
--   Claim EC.3 — the revenue is a nonnegative power series in the spectrum, (EC.17)–(EC.18)
-- statement:
--   Fix $\mu\in[0,1]$, $\delta\in(0,1)$, $\alpha,\beta>0$, $\tau\in\{0,1,2,\dots\}$ and $p\in[0,\alpha/\beta]$. Then there are sequences $(a_k)_{k\ge0}$ and $(b_k)_{k\ge0}$ with $a_k\ge0$ and $b_k\ge0$ for all $k$, depending only on these scalars, such that for every network $M$ on any number $n$ of consumers satisfying Assumption 1 and every orthonormal eigenbasis $v_1,\dots,v_n$ of $M$ with eigenvalues $\lambda_i$ (so $\hat\lambda_i=\lambda_i+\mu$),
--
--   $$J(\mathbf 0;\tau,p)=\sum_{k=0}^{\infty}a_k\sum_{i=1}^{n}\hat\lambda_i^{k}\langle v_i,\mathbf 1\rangle^2\qquad\text{(EC.17)}$$
--
--   $$J(\mathbf 0;\tau,p)=\sum_{k=0}^{\infty}b_k\sum_{i=1}^{n}\lambda_i^{k}\langle v_i,\mathbf 1\rangle^2\qquad\text{(EC.18)}$$
--
--   with both series convergent. Since $\sum_i\lambda_i^k\langle v_i,\mathbf 1\rangle^2=\langle M^k\mathbf 1,\mathbf 1\rangle$ is the weighted number of walks of length $k$, (EC.18) shows the revenue of a fixed policy is a nonnegative combination of walk counts.
--
--   Differences from the source:
--   - reading: a_k, b_k independent of the eigenvalues and eigenvectors → ∃ a b chosen before the network, its size n and its eigenbasis; reason: independence means the coefficients cannot depend on the network; they depend only on α, β, δ, μ, τ, p
--   - generalization: v_i, λ̂_i the eigenvectors and eigenvalues of M̂ → any orthonormal eigenbasis v of M with eigenvalues lam, and λ̂_i = lam i + μ; reason: an eigenbasis of M is exactly an eigenbasis of M̂ = M + μI with eigenvalues shifted by μ (Fact 3); the paper fixes one unspecified eigenbasis, and the statement for every one specializes to it
--   - encoding: equalities of infinite sums → HasSum (unconditional convergence in ℝ to the revenue); reason: in ℝ unconditional convergence is absolute convergence, which the paper's rearrangement uses
--   - reading: α, β constant coefficients → 0 < α, 0 < β; reason: the quadratic term of (1) has the negative sign to induce concavity, which needs β > 0, and the price cap α/β with nonnegative prices needs α ≥ 0; standing assumption of every statement
--   - reading: given τ and p → τ ∈ ℕ and p ∈ [0, α/β]; reason: the policy class of the mission (see Policy): (2) is valid "provided that x*i,t > 0" and (4) is written "for any fixed price p ≤ α/β"; p(α − βp) ≥ 0, which a_k ≥ 0 needs, holds exactly on this domain
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, Claim EC.3, (EC.17)–(EC.18), p.ec11

import Mathlib
import Definitions.Def_NetServicePricing_IsNetwork
import Definitions.Def_NetServicePricing_Assumption1
import Definitions.Def_NetServicePricing_revenue

open Matrix

namespace NetServicePricing

/-- **Claim EC.3 (the revenue as a nonnegative power series in the spectrum).**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, Claim EC.3, p.ec11: "For given τ and p, the discounted revenue J(0;τ,p) given by (EC.2)
can be expressed as the following infinite sums:
J(0;τ,p) = ∑_{k=0}^∞ ak ∑_{i=1}^n λ̂i^k⟨vi,1⟩² (EC.17)
J(0;τ,p) = ∑_{k=0}^∞ bk ∑_{i=1}^n λi^k⟨vi,1⟩² (EC.18)
where ak,bk ≥ 0, for all k ∈ Z+, and they are independent of the eigenvalues and eigenvectors."

Fix `μ ∈ [0,1]`, `δ ∈ (0,1)`, `α, β > 0`, `τ ∈ ℕ` and `p ∈ [0, α/β]`. There are nonnegative
sequences `a, b` such that for every number of consumers `n`, every network `M` satisfying
Assumption 1 and every orthonormal eigenbasis `v` of `M` with eigenvalues `λᵢ`
(`λ̂ᵢ = λᵢ + μ`), both series converge to `J(0;τ,p)`.

**Formalization Note** The sequences are chosen before the network: this is the content of
"independent of the eigenvalues and eigenvectors"; choosing them before `n` too is harmless,
since they depend only on `α, β, δ, μ, τ, p`. Convergence is stated as `HasSum` (unconditional,
i.e. absolute, convergence in `ℝ`). `⟨vᵢ, 𝟏⟩ = ∑ⱼ vᵢⱼ`. -/
theorem claim_EC_3 (μ δ α β : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hα : 0 < α) (hβ : 0 < β) (τ : ℕ) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) (α / β)) :
    ∃ a b : ℕ → ℝ, (∀ k, 0 ≤ a k ∧ 0 ≤ b k) ∧
      ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ), IsNetwork M → Assumption1 M μ δ →
        ∀ (v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (lam : Fin n → ℝ),
          (∀ i, M *ᵥ ⇑(v i) = lam i • ⇑(v i)) →
          HasSum (fun k : ℕ => a k * ∑ i, (lam i + μ) ^ k * (∑ j, v i j) ^ 2)
              (revenue M μ α β δ τ p) ∧
            HasSum (fun k : ℕ => b k * ∑ i, lam i ^ k * (∑ j, v i j) ^ 2)
              (revenue M μ α β δ τ p) := by sorry

end NetServicePricing
