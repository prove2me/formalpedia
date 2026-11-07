-- Prove2me | Theorems.Thm_GraphTensorCP_corollary_3_5
-- name    : GraphTensorCP.corollary_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:02.896826+00:00
-- url     : https://prove2.me/theorems/b9a58232-a0d5-47fa-884e-34cabd242ed6
-- title:
--   Corollary 3.5 — entropy inequality $\phi(A)\ge e^{P^{(\phi)}_{k-1,k}H(\theta)}\prod_i\phi(A_i)^{\theta_i}$ for aligned partial sums
-- statement:
--   Let $k\ge2$ and $s\ge1$ be integers, and let $A=A_1\boxplus_e\cdots\boxplus_e A_s$ with $e=(k-1,k)$, where the nonzero tensors $A_1,\dots,A_s$ have aligned shared coordinates. Let $\phi\in\Phi_{k,\mathbb F}$ and let $P^{(\phi)}_{k-1,k}$ be its spectral edge weight. Then for every probability vector $\theta=(\theta_1,\dots,\theta_s)$,
--
--   $$\phi(A)\ge\exp\big(P^{(\phi)}_{k-1,k}\,H(\theta_1,\dots,\theta_s)\big)\prod_{i=1}^s\phi(A_i)^{\theta_i},$$
--
--   where $H(\theta_1,\dots,\theta_s)=-\sum_i\theta_i\ln\theta_i$ (natural logarithm, $0\ln0=0$).
--
--   The inequality turns the separation construction into a gain on spectral values; the concavity and tripling lemmas of Section 4 are its two applications.
--
--   **Formalization Note** The partial sum is the predicate `IsAlignedPartialSum A B` with blocks `B : Fin s → MME.TensorObj K k`; "nonzero" means the block's tensor is nonzero. The legs $e=(k-1,k)$ are the 0-based indices $k-2,k-1$. The entropy is $\sum_i$ `Real.negMulLog` $(\theta_i)$.
--
--   Differences from the source:
--   - encoding: spectral points $\phi:\mathrm{Tens}_n(\mathbb F)\to\mathbb R_{\ge0}$ (Definition 2.19) → monotone semiring homomorphisms on the published quotient `MME.TensorQ` by mutual restriction (`Spec K n hn`); reason: a spectral point is constant on mutual-restriction classes and its four conditions are exactly "monotone semiring homomorphism"; same set of maps
--   - generalization: $A=A_1\boxplus_e\cdots\boxplus_e A_s$ in the coordinates of Definition 2.9 → any $A$ with linear maps that are bijective on the shared legs, injective with independent images on legs $k-1,k$, and send $\sum_h A_h$ to $A$ (`IsAlignedPartialSum`); reason: the paper's partial sum satisfies the predicate (sector inclusions, identity on shared legs); every instance is a paper partial sum of blocks isomorphic to the $A_h$ padded with zero coordinates, which leaves all spectral values unchanged, so the statement specializes to the paper's
--   - encoding: legs $k-1,k$ → 0-based indices $k-2,k-1$; reason: relabeling
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Corollary 3.5, p.33

import Mathlib
import Definitions.Def_GraphTensorCP_specWeight
import Definitions.Def_GraphTensorCP_IsAlignedPartialSum

universe u

namespace GraphTensorCP

/-- **Corollary 3.5** (entropy inequality), Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), p.33:
"Let k ≥ 2 and s ≥ 1 be integers. Let A = A₁ ⊞_e · · · ⊞_e A_s, where e = (k − 1, k) and the nonzero
tensors A₁, . . . , A_s have aligned shared coordinates as in Definition 2.9. Let ϕ ∈ Φ_{k,F} and let
P^{(ϕ)}_{k−1,k} be its spectral edge weight from Definition 2.24. For every probability vector
θ = (θ₁, . . . , θ_s), ϕ(A) ≥ exp( P^{(ϕ)}_{k−1,k} H(θ₁, . . . , θ_s) ) ∏_{i=1}^{s} ϕ(A_i)^{θ_i}, where
H(θ₁, . . . , θ_s) = −Σ_{i=1}^{s} θ_i ln θ_i and 0 ln 0 = 0."

**Formalization Note.** Blocks are `B : Fin s → MME.TensorObj K k`; the partial sum is the predicate
`IsAlignedPartialSum A B`. The legs `e = (k−1, k)` are the 0-based indices `k−2, k−1`. "Nonzero" is
`(B h).t ≠ 0`. The entropy uses the natural logarithm: `H = Σ_h Real.negMulLog (θ h)`, which has
`0 ln 0 = 0` built in; `exp` is `Real.exp`; the powers are `Real.rpow`. -/
theorem corollary_3_5 {K : Type u} [Field K] {k s : ℕ} (hk : 1 < k) (hs : 1 ≤ s)
    (A : MME.TensorObj K k) (B : Fin s → MME.TensorObj K k) (hAB : IsAlignedPartialSum A B)
    (hB : ∀ h, (B h).t ≠ 0) (φ : Spec K k hk) (θ : Fin s → ℝ) (hθ0 : ∀ h, 0 ≤ θ h)
    (hθ1 : ∑ h, θ h = 1) :
    Real.exp (specWeight φ ⟨k - 2, by omega⟩ ⟨k - 1, by omega⟩ * ∑ h, Real.negMulLog (θ h)) *
        ∏ h, φ (MME.TensorQ.toQ (B h)) ^ θ h ≤ φ (MME.TensorQ.toQ A) := by sorry

end GraphTensorCP
