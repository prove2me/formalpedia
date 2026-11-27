-- Prove2me | Theorems.Thm_MultiStageAlloc_Supplement_corollary_1
-- name    : MultiStageAlloc.Supplement.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:20:50.079651+00:00
-- url     : https://prove2.me/theorems/a9cb1bed-c933-53f5-89b6-585b81797d95
-- title:
--   Corollary 1 (corrected: summand $\eta_{j,\tau'}$) — distribution monotonicity and only disposing smallest
-- statement:
--   Fix a stage $k\in[K-1]$ and a state $\eta$ with $\eta_{j,\tau}\ge0$ and $\sum_{\tau\in[T]}\eta_{j,\tau}\le1$ for every advertiser $j$. Let $(x^*,y^*,z^*)$ be an optimal solution of $\mathcal P^{\mathrm{MCA}}_k$ given $\eta$. Then for every advertiser $j\in V$ and $\tau\in[T]$:
--
--   1. (Distribution Monotonicity)
--   $$
--   H_{j,\tau}(x^*,y^*)\ \ge\ \sum_{\tau'=\tau}^{T}\eta_{j,\tau'} ;
--   $$
--   2. (Only Disposing Smallest)
--   $$
--   \sum_{\tau'=\tau}^{T}\bigl(\eta_{j,\tau'}-y^*_{j,\tau'}\bigr)=\sum_{\tau'=\tau}^{T}\bigl(\eta_{j,\tau'}-y^*_{j,\tau'}\bigr)\,f_k\bigl(H_{j,\tau}(x^*,y^*)\bigr).
--   $$
--
--   Here $f_k$ is the polynomial of Proposition 1. The first bullet says that after stage $k$ the mass at prices at least $\hat w_\tau$ never decreases. The second says that whenever impressions at levels $\ge\tau$ are disposed, $f_k(H_{j,\tau})=1$, i.e. $H_{j,\tau}=1$. Both identities enter Step i of the proof of Theorem 2.
--
--   Differences from the source:
--   - correction: (Distribution Monotonicity) H_{j,τ}(x∗, y∗) ≥ Σ_{τ′≥τ} η^(k−1)_{j,τ} → H_{j,τ}(x, y) ≥ Σ_{τ′=τ}^{T} η_{j,τ′}; reason: as printed the sum is (T − τ + 1)·η_{j,τ}; take K = 3, T = 2, one advertiser and one stage-1 user whose only configuration gives it one impression at price ŵ_1 (stage-2 and stage-3 users with ξ ≡ 0 give |U_k| ≥ 1 and change nothing): the stage-1 optimum is x = z = 1 (the objective ŵ_1(x − F_1(x)) has derivative ŵ_1(1 − f_1(x)) > 0 on [0, 1)), so η^(1)_{j,1} = 1, and the printed bullet at k = 2, τ = 1 claims H_{j,1} ≥ 2 while every feasible point has H_{j,1} ≤ 1; the summation index τ′ is the intended one, as in the second bullet and in H_{j,τ}(x^(k), y^(k)) = Σ_{τ′≥τ} η^(k)_{j,τ′} on p.27
--   - generalization: the state η^(k−1) of a run of Algorithm 2 → any state η with η_{j,τ} ≥ 0 and Σ_{τ∈[T]} η_{j,τ} ≤ 1 for every j; reason: every state of a run satisfies both (η^(k) is a sum of non-negative variables, and Σ_τ η^(k)_{j,τ} is the left side of the capacity constraint of P^MCA_k), so the run case is a special case
--   - reading: “(x∗, y∗, z∗) is the optimal solution of P^MCA_k” → (x, y, z) is any optimal solution; reason: the optimum need not be unique; the proof of Theorem 2 applies the lemma to whichever optimum the run chose
--   - generalization: batches U_k with |U_k| ≥ 1 (§2.1, carried to §2.2 by “similar to our baseline model”) → batches, and the sets U, C, V, may be empty; reason: an empty batch is the same as a batch of one dummy user with ξ ≡ 0 (its x is forced to 0 and its z enters no objective), so every instance of the source is one of the Lean's and the extra instances add nothing the source's instances do not already contain
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Corollary 1, p.28 (proof in Appendix B.5)

import Mathlib
import Definitions.Def_MultiStageAlloc_Supplement_StageProgramMCA

namespace MultiStageAlloc.Supplement

/-- **Corollary 1.** Feng & Niazadeh, *Batching and Optimal Multi-stage Bipartite Allocations*,
arXiv:2211.16581v1, p.28. Fix `k ∈ [K - 1]` and let `(x, y, z)` be an optimal solution of
(P^MCA_k). For every advertiser `j` and `τ ∈ [T]`:
* (Distribution Monotonicity) `H_{j,τ}(x, y) ≥ ∑_{τ' ≥ τ} η^(k-1)_{j,τ'}`;
* (Only Disposing Smallest)
  `∑_{τ' ≥ τ} (η^(k-1)_{j,τ'} - y_{j,τ'}) = ∑_{τ' ≥ τ} (η^(k-1)_{j,τ'} - y_{j,τ'}) · f_k(H_{j,τ}(x, y))`.

**Formalization Note.** The page prints the first summand as `η^(k-1)_{j,τ}`, with the summation
index `τ'` unused; it is read as `η^(k-1)_{j,τ'}`, matching the second bullet and the identity
`H_{j,τ}(x^(k), y^(k)) = ∑_{τ' ≥ τ} η^(k)_{j,τ'}` of p.27. Sums over `τ' ≥ τ` run over
`τ ≤ τ' ≤ T`. The state `η` is any vector with `η ≥ 0` and `∑_{τ ∈ [T]} η_{j,τ} ≤ 1` for each `j`,
which every state `η^(k-1)` of a run of Algorithm 2 satisfies. `f_k = regPoly K k`. -/
theorem corollary_1 {U C V : Type*} [Fintype U] [Fintype C] [Fintype V] {K : ℕ}
    (I : MCAInstance U C V K) (k : ℕ) (hk1 : 1 ≤ k) (hkK : k < K) (η : V → ℕ → ℝ)
    (hη0 : ∀ j τ, τ ∈ Finset.Icc 1 I.T → 0 ≤ η j τ)
    (hη1 : ∀ j, ∑ τ ∈ Finset.Icc 1 I.T, η j τ ≤ 1)
    (x : U → C → V → ℝ) (y : V → ℕ → ℝ) (z : U → C → ℝ)
    (hopt : IsMCAStageOptimal I k η x y z) :
    ∀ j τ, τ ∈ Finset.Icc 1 I.T →
      (∑ τ' ∈ Finset.Icc τ I.T, η j τ') ≤ levelH I k x y j τ ∧
      ∑ τ' ∈ Finset.Icc τ I.T, (η j τ' - y j τ') =
        ∑ τ' ∈ Finset.Icc τ I.T, (η j τ' - y j τ') * regPoly K k (levelH I k x y j τ) := by sorry

end MultiStageAlloc.Supplement
