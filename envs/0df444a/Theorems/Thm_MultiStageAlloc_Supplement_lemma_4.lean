-- Prove2me | Theorems.Thm_MultiStageAlloc_Supplement_lemma_4
-- name    : MultiStageAlloc.Supplement.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:21:42.985801+00:00
-- url     : https://prove2.me/theorems/1890526d-fc38-4729-90c0-59abec858147
-- title:
--   Lemma 4 — low and high prices of the last stage in an optimal solution of LP-$\mathcal D_K$
-- statement:
--   Let $\eta$ be the last-stage state and let $(\lambda^*,\theta^*,\mu^*,\pi^*)$ be an optimal solution of the dual program LP-$\mathcal D_K$. Then for every advertiser $j\in V$ and every $\tau\in[T]$:
--
--   1. (Low Prices of Last Stage) if $\hat w_\tau\le\theta^*_j$, then $\eta_{j,\tau}\,\pi^*_{j,\tau}=0$;
--   2. (High Prices of Last Stage) if $\hat w_\tau>\theta^*_j$, then $\eta_{j,\tau}\,(\hat w_\tau-\pi^*_{j,\tau})=\eta_{j,\tau}\,\theta^*_j$.
--
--   At the last stage $F_K\equiv0$, so the dual price $\theta^*_j$ of advertiser $j$ may be positive, unlike in Lemma 2. The lemma describes how the carried-over impressions at each price level are valued against $\theta^*_j$. It is used for the approximate dual feasibility at stage $K$ in the proof of Theorem 2.
--
--   **Formalization Note** The state $\eta$ is an arbitrary real vector. The page's $\eta^{(K-1)}$, the state of a run before its last stage, is a special case.
--
--   Differences from the source:
--   - generalization: the state η^(K−1) of a run of Algorithm 2 → an arbitrary state η : V → ℕ → ℝ; reason: η^(K−1) is one such vector, so the run case is a special case
--   - reading: “(λ∗, θ∗, µ∗, π∗) is the optimal solution of LP-D_K” → any optimal (feasible and minimizing) solution; reason: an LP optimum need not be unique; the proof of Theorem 2 uses whichever optimum it fixes
--   - generalization: batches U_k with |U_k| ≥ 1 (§2.1, carried to §2.2 by “similar to our baseline model”) → batches, and the sets U, C, V, may be empty; reason: an empty batch is the same as a batch of one dummy user with ξ ≡ 0 (its x is forced to 0 and its z enters no objective), so every instance of the source is one of the Lean's and the extra instances add nothing the source's instances do not already contain
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Lemma 4, p.29 (proof in Appendix B.6)

import Mathlib
import Definitions.Def_MultiStageAlloc_Supplement_LPDK

namespace MultiStageAlloc.Supplement

/-- **Lemma 4 (Low and High Prices of the Last Stage).** Feng & Niazadeh, *Batching and Optimal
Multi-stage Bipartite Allocations*, arXiv:2211.16581v1, p.29. Let `(λ, θ, µ, π)` be an optimal
solution of the dual program (LP-D_K) for the last-stage state `η = η^(K-1)`. For every advertiser
`j` and `τ ∈ [T]`:
* (Low Prices of Last Stage) if `ŵ_τ ≤ θ_j` then `η_{j,τ} π_{j,τ} = 0`;
* (High Prices of Last Stage) if `ŵ_τ > θ_j` then `η_{j,τ} (ŵ_τ - π_{j,τ}) = η_{j,τ} θ_j`.

**Formalization Note.** The state `η` is an arbitrary real vector; the state `η^(K-1)` of a run of
Algorithm 2 is a special case. -/
theorem lemma_4 {U C V : Type*} [Fintype U] [Fintype C] [Fintype V] {K : ℕ}
    (I : MCAInstance U C V K) (η : V → ℕ → ℝ)
    (lam : U → ℝ) (θ : V → ℝ) (μ : U → C → V → ℝ) (π : V → ℕ → ℝ)
    (hopt : IsLPDKOptimal I η lam θ μ π) :
    ∀ j τ, τ ∈ Finset.Icc 1 I.T →
      (I.wgrid τ ≤ θ j → η j τ * π j τ = 0) ∧
      (θ j < I.wgrid τ → η j τ * (I.wgrid τ - π j τ) = η j τ * θ j) := by sorry

end MultiStageAlloc.Supplement
