-- Prove2me | Theorems.Thm_MultiStageAlloc_Supplement_lemma_2
-- name    : MultiStageAlloc.Supplement.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:19:47.360224+00:00
-- url     : https://prove2.me/theorems/9a8fb631-51d2-5d53-a466-5b912b857828
-- title:
--   Lemma 2 (Duality-based Connection) — KKT multipliers of $\mathcal P^{\mathrm{MCA}}_k$ with $\theta^*=0$
-- statement:
--   Fix a stage $k\in[K-1]$ (so $1\le k<K$) and a state $\eta$ with $\eta_{j,\tau}\ge0$ and $\sum_{\tau\in[T]}\eta_{j,\tau}\le1$ for every advertiser $j$. Let $(x^*,y^*,z^*)$ be an optimal solution of the stage program $\mathcal P^{\mathrm{MCA}}_k$ given $\eta$. Then there exist non-negative multipliers $(\lambda^*,\theta^*,\mu^*,\psi^*,\phi^*)$ with $\theta^*_j=0$ for every $j\in V$ such that, for every user $i\in U_k$, configuration $c\in C$ and advertiser $j\in V$:
--
--   1. (complementary slackness) $\lambda^*_i\bigl(\sum_{c\in C}z^*_{i,c}-1\bigr)=0$, $\mu^*_{i,c,j}\bigl(x^*_{i,c,j}-\xi_{i,c,j}z^*_{i,c}\bigr)=0$, $\psi^*_{i,c,j}x^*_{i,c,j}=0$ and $\phi^*_{i,c}z^*_{i,c}=0$;
--   2. (stationarity-1) $\sum_{j\in V}\xi_{i,c,j}\mu^*_{i,c,j}-\lambda^*_i+\phi^*_{i,c}=0$;
--   3. (stationarity-2)
--   $$
--   w_{i,c,j}-\sum_{\tau\in[T]:\ \hat w_\tau\le w_{i,c,j}}(\hat w_\tau-\hat w_{\tau-1})\,f_k\bigl(H_{j,\tau}(x^*,y^*)\bigr)-\mu^*_{i,c,j}+\psi^*_{i,c,j}=0 .
--   $$
--
--   Here $f_k$ is the polynomial of Proposition 1 and $H_{j,\tau}$ the mass advertiser $j$ holds at prices at least $\hat w_\tau$. The multipliers $\lambda^*_i$ and $\mu^*_{i,c,j}$ become the dual variables $\alpha_i$ and $\gamma_{i,c,j}$ of stage $k$ in the dual-fitting proof of Theorem 2.
--
--   **Formalization Note** The page's "for all $(i,c,j)\in E_k$" is read as $i\in U_k$, $c\in C$, $j\in V$, because the configuration model has no edge set.
--
--   Differences from the source:
--   - generalization: the state η^(k−1) of a run of Algorithm 2 → any state η with η_{j,τ} ≥ 0 and Σ_{τ∈[T]} η_{j,τ} ≤ 1 for every j; reason: every state of a run satisfies both (η^(k) is a sum of non-negative variables, and Σ_τ η^(k)_{j,τ} is the left side of the capacity constraint of P^MCA_k), so the run case is a special case
--   - reading: “(x∗, y∗, z∗) is the optimal solution of P^MCA_k” → (x, y, z) is any optimal solution; reason: the optimum need not be unique; the proof of Theorem 2 applies the lemma to whichever optimum the run chose
--   - reading: “for all (i, c, j) ∈ E_k”, with θ∗_j = 0 listed inside that block → i ∈ U_k, c ∈ C, j ∈ V; θ_j = 0 for every j ∈ V; reason: the configuration model defines no edge set, and the page uses E_k for the triples of the stage-k users (p.30); θ∗_j = 0 does not involve i or c
--   - generalization: batches U_k with |U_k| ≥ 1 (§2.1, carried to §2.2 by “similar to our baseline model”) → batches, and the sets U, C, V, may be empty; reason: an empty batch is the same as a batch of one dummy user with ξ ≡ 0 (its x is forced to 0 and its z enters no objective), so every instance of the source is one of the Lean's and the extra instances add nothing the source's instances do not already contain
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Lemma 2, pp.27–28 (proof in Appendix B.3)

import Mathlib
import Definitions.Def_MultiStageAlloc_Supplement_StageProgramMCA

namespace MultiStageAlloc.Supplement

/-- **Lemma 2 (Duality-based Connection).** Feng & Niazadeh, *Batching and Optimal Multi-stage
Bipartite Allocations*, arXiv:2211.16581v1, pp.27–28. Fix a stage `k ∈ [K - 1]` and let
`(x, y, z)` be an optimal solution of (P^MCA_k). Then there are non-negative multipliers
`(λ, θ, µ, ψ, φ)` with `θ = 0` such that, for every user `i ∈ U_k`, configuration `c` and advertiser
`j`, complementary slackness, stationarity-1 and stationarity-2 hold:
`λ_i (∑_c z_{i,c} - 1) = 0`, `µ_{i,c,j} (x_{i,c,j} - ξ_{i,c,j} z_{i,c}) = 0`, `ψ_{i,c,j} x_{i,c,j} = 0`,
`φ_{i,c} z_{i,c} = 0`, `∑_j ξ_{i,c,j} µ_{i,c,j} - λ_i + φ_{i,c} = 0`, and
`w_{i,c,j} - ∑_{τ ∈ [T] : ŵ_τ ≤ w_{i,c,j}} (ŵ_τ - ŵ_{τ-1}) f_k(H_{j,τ}(x, y)) - µ_{i,c,j} + ψ_{i,c,j} = 0`.

**Formalization Note.** The page's "for all `(i, c, j) ∈ E_k`" reads as `i ∈ U_k, c ∈ C, j ∈ V`
(the configuration model has no edge set). `θ_j = 0` is stated for every `j`. The state `η` is any
vector with `η ≥ 0` and `∑_{τ ∈ [T]} η_{j,τ} ≤ 1` for each `j`, which every state `η^(k-1)` of a run
of Algorithm 2 satisfies. `f_k = regPoly K k`. -/
theorem lemma_2 {U C V : Type*} [Fintype U] [Fintype C] [Fintype V] {K : ℕ}
    (I : MCAInstance U C V K) (k : ℕ) (hk1 : 1 ≤ k) (hkK : k < K) (η : V → ℕ → ℝ)
    (hη0 : ∀ j τ, τ ∈ Finset.Icc 1 I.T → 0 ≤ η j τ)
    (hη1 : ∀ j, ∑ τ ∈ Finset.Icc 1 I.T, η j τ ≤ 1)
    (x : U → C → V → ℝ) (y : V → ℕ → ℝ) (z : U → C → ℝ)
    (hopt : IsMCAStageOptimal I k η x y z) :
    ∃ (lam : U → ℝ) (θ : V → ℝ) (μ ψ : U → C → V → ℝ) (φ : U → C → ℝ),
      (∀ i, 0 ≤ lam i) ∧ (∀ j, 0 ≤ θ j) ∧ (∀ i c j, 0 ≤ μ i c j) ∧ (∀ i c j, 0 ≤ ψ i c j) ∧
      (∀ i c, 0 ≤ φ i c) ∧ (∀ j, θ j = 0) ∧
      ∀ i c j, I.batch i = k →
        lam i * (∑ c', z i c' - 1) = 0 ∧
        μ i c j * (x i c j - I.ξ i c j * z i c) = 0 ∧
        ψ i c j * x i c j = 0 ∧
        φ i c * z i c = 0 ∧
        (∑ j', I.ξ i c j' * μ i c j') - lam i + φ i c = 0 ∧
        I.price i c j -
            (∑ τ ∈ (Finset.Icc 1 I.T).filter (fun τ => I.wgrid τ ≤ I.price i c j),
              (I.wgrid τ - I.wgrid (τ - 1)) * regPoly K k (levelH I k x y j τ)) -
            μ i c j + ψ i c j = 0 := by sorry

end MultiStageAlloc.Supplement
