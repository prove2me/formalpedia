-- Prove2me | Theorems.Thm_MultiStageAlloc_Supplement_lemma_3
-- name    : MultiStageAlloc.Supplement.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:20:30.951199+00:00
-- url     : https://prove2.me/theorems/2ce39aae-b8ec-4339-b7c0-f9ec01ddfb24
-- title:
--   Lemma 3 (Disposing Smallest Price) — preemption at level $\tau$ forces $H_{j,\tau}=1$
-- statement:
--   Fix a stage $k\in[K-1]$ and a state $\eta$ with $\eta_{j,\tau}\ge0$ and $\sum_{\tau\in[T]}\eta_{j,\tau}\le1$ for every advertiser $j$. Let $(x^*,y^*,z^*)$ be an optimal solution of $\mathcal P^{\mathrm{MCA}}_k$ given $\eta$. Then, for every advertiser $j\in V$ and every price level $\tau\in[T]$,
--   $$
--   \eta_{j,\tau}-y^*_{j,\tau}>0\quad\Longrightarrow\quad H_{j,\tau}(x^*,y^*)=1 .
--   $$
--
--   In words: if the algorithm preempts impressions of advertiser $j$ that were bought at price $\hat w_\tau$, then $j$'s capacity is exhausted by impressions at prices at least $\hat w_\tau$. Preemption therefore only disposes of the cheapest impressions. The lemma is used in Step i of the proof of Theorem 2 and yields Corollary 1.
--
--   Differences from the source:
--   - generalization: the state η^(k−1) of a run of Algorithm 2 → any state η with η_{j,τ} ≥ 0 and Σ_{τ∈[T]} η_{j,τ} ≤ 1 for every j; reason: every state of a run satisfies both (η^(k) is a sum of non-negative variables, and Σ_τ η^(k)_{j,τ} is the left side of the capacity constraint of P^MCA_k), so the run case is a special case
--   - reading: “(x∗, y∗, z∗) is the optimal solution of P^MCA_k” → (x, y, z) is any optimal solution; reason: the optimum need not be unique; the proof of Theorem 2 applies the lemma to whichever optimum the run chose
--   - generalization: batches U_k with |U_k| ≥ 1 (§2.1, carried to §2.2 by “similar to our baseline model”) → batches, and the sets U, C, V, may be empty; reason: an empty batch is the same as a batch of one dummy user with ξ ≡ 0 (its x is forced to 0 and its z enters no objective), so every instance of the source is one of the Lean's and the extra instances add nothing the source's instances do not already contain
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Lemma 3, p.28 (proof in Appendix B.4)

import Mathlib
import Definitions.Def_MultiStageAlloc_Supplement_StageProgramMCA

namespace MultiStageAlloc.Supplement

/-- **Lemma 3 (Disposing Smallest Price).** Feng & Niazadeh, *Batching and Optimal Multi-stage
Bipartite Allocations*, arXiv:2211.16581v1, p.28. Fix `k ∈ [K - 1]` and let `(x, y, z)` be an
optimal solution of (P^MCA_k). For every advertiser `j` and `τ ∈ [T]`, if
`η^(k-1)_{j,τ} - y_{j,τ} > 0` then `H_{j,τ}(x, y) = 1`.

**Formalization Note.** The state `η` is any vector with `η ≥ 0` and `∑_{τ ∈ [T]} η_{j,τ} ≤ 1` for
each `j`, which every state `η^(k-1)` of a run of Algorithm 2 satisfies. -/
theorem lemma_3 {U C V : Type*} [Fintype U] [Fintype C] [Fintype V] {K : ℕ}
    (I : MCAInstance U C V K) (k : ℕ) (hk1 : 1 ≤ k) (hkK : k < K) (η : V → ℕ → ℝ)
    (hη0 : ∀ j τ, τ ∈ Finset.Icc 1 I.T → 0 ≤ η j τ)
    (hη1 : ∀ j, ∑ τ ∈ Finset.Icc 1 I.T, η j τ ≤ 1)
    (x : U → C → V → ℝ) (y : V → ℕ → ℝ) (z : U → C → ℝ)
    (hopt : IsMCAStageOptimal I k η x y z) :
    ∀ j τ, τ ∈ Finset.Icc 1 I.T → 0 < η j τ - y j τ → levelH I k x y j τ = 1 := by sorry

end MultiStageAlloc.Supplement
