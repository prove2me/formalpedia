-- Prove2me | Theorems.Thm_NetServicePricing_eq_EC_19
-- name    : NetServicePricing.eq_EC_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:59.341247+00:00
-- url     : https://prove2.me/theorems/c49dfbff-c331-4cac-841f-e6ab0eeb0316
-- title:
--   (EC.19) — every network has at least as many walks as the complete network: $\sum_i\lambda_i^k\langle v_i,\mathbf 1\rangle^2\ge n\mathcal D^k$
-- statement:
--   Let $M$ be a network on $n$ consumers with average degree $\mathcal D$, let $v_1,\dots,v_n$ be an orthonormal eigenbasis of $M$ with eigenvalues $\lambda_i$, and let $v^C_1,\dots,v^C_n$ be an orthonormal eigenbasis, with eigenvalues $\lambda^C_i$, of the complete network $C$ with average degree $\mathcal D$ (off-diagonal weights $\mathcal D/(n-1)$). Then for every $k\in\{0,1,2,\dots\}$,
--
--   $$\sum_{i=1}^{n}\lambda_i^k\langle v_i,\mathbf 1\rangle^2\ \ge\ \sum_{i=1}^{n}(\lambda^C_i)^k\langle v^C_i,\mathbf 1\rangle^2\ =\ n\mathcal D^k .$$
--
--   Both sides count weighted walks of length $k$; combined with Claim EC.3 term by term, this is the comparison behind part (ii) of Theorem 2.
--
--   Differences from the source:
--   - generalization: a network M of the class of Theorem 2 (Assumption 1 standing) → any network M, without Assumption 1; reason: (EC.19) is a fact about walk counts that does not use Assumption 1; it specializes to the networks of the class
--   - generalization: the eigenvalues and eigenvectors of M and of the complete network → any orthonormal eigenbases of M and of C; reason: the paper fixes unspecified eigenbases; the statement for every one specializes to them
--   - encoding: k ∈ Z₊ → k ∈ ℕ, with 0 ^ 0 = 1; reason: the sum over k = 0 in (EC.17)–(EC.18) uses the same convention
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, EC.3.2 (proof of Theorem 2), (EC.19), p.ec11

import Mathlib
import Definitions.Def_NetServicePricing_IsNetwork
import Definitions.Def_NetServicePricing_averageDegree
import Definitions.Def_NetServicePricing_completeNetwork

open Matrix

namespace NetServicePricing

/-- **(EC.19): walks of length `k` are fewest in the complete network.**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, EC.3.2, proof of Theorem 2, (EC.19), p.ec11:
"∑_{i=1}^n λi^k⟨vi,1⟩² ≥ ∑_{i=1}^n (λi^C)^k⟨vi^C,1⟩² = nD^k, k ∈ Z+ (EC.19)
where λi^C and vi^C are the eigenvalues and eigenvectors of a complete network with average
degree D."

For every network `M` with average degree `D`, every orthonormal eigenbasis `v` of `M` with
eigenvalues `λᵢ`, every orthonormal eigenbasis `v^C` of the complete network `C` with average
degree `D` (off-diagonal weight `D/(n − 1)`) with eigenvalues `λᵢ^C`, and every `k ∈ ℕ`:
`∑ᵢ (λᵢ^C)^k ⟨vᵢ^C,𝟏⟩² ≤ ∑ᵢ λᵢ^k ⟨vᵢ,𝟏⟩²` and `∑ᵢ (λᵢ^C)^k ⟨vᵢ^C,𝟏⟩² = n D^k`.

**Formalization Note** `⟨vᵢ, 𝟏⟩ = ∑ⱼ vᵢⱼ`. Assumption 1 is not required. For `n = 1`, `D = 0` and
`C = 0`; `0 ^ 0 = 1`. -/
theorem eq_EC_19 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsNetwork M) (D : ℝ)
    (hD : averageDegree M = D)
    (v : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (lam : Fin n → ℝ)
    (hv : ∀ i, M *ᵥ ⇑(v i) = lam i • ⇑(v i))
    (vC : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (lamC : Fin n → ℝ)
    (hvC : ∀ i, completeNetwork n D *ᵥ ⇑(vC i) = lamC i • ⇑(vC i)) (k : ℕ) :
    ∑ i, lamC i ^ k * (∑ j, vC i j) ^ 2 ≤ ∑ i, lam i ^ k * (∑ j, v i j) ^ 2 ∧
      ∑ i, lamC i ^ k * (∑ j, vC i j) ^ 2 = (n : ℝ) * D ^ k := by sorry

end NetServicePricing
