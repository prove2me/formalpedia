-- Prove2me | Theorems.Thm_GraphSimOT_Gaps_lemma_30
-- name    : GraphSimOT.Gaps.lemma_30
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:07:46.595648+00:00
-- url     : https://prove2.me/theorems/93d363e8-f7b9-46d3-9e7a-57c1a771cf4a
-- title:
--   Lemma 30 — dependent rounding of a bipartite fractional matching with marginals (1−γ)q and tail exp(−µγ(2τ−3)/20) [CVZ11]
-- statement:
--   Let $E\subseteq V\times W$ be the edge set of a finite bipartite graph, $q$ a point of its bipartite matching polytope (the convex hull of the indicator vectors of its matchings) and $\gamma\in(0,\frac12]$. Then there is a random matching $M$ of $E$ with $\mathbb E[1_M] = (1-\gamma)q$ such that for every linear statistic $Z = \sum_e\alpha_e 1[e\in M]$ with $\alpha_e\in[0,1]$, every $\mu\ge\mathbb E[Z]$ with $\mu>0$, and every $\tau\ge2$,
--   $$\Pr(Z\ge\tau\mu)\ \le\ \exp\Big(-\frac{\mu\gamma(2\tau-3)}{20}\Big).\qquad(19)$$
--
--   The paper cites this special case of the dependent rounding scheme of Chekuri, Vondrák and Zenklusen [CVZ11, Theorem 1.1] and applies it to $q = Q$ on $\mathrm{supp}(Q)$ to obtain a large matching with small local costs (Lemma 31).
--
--   **Formalization Note.** The random matching is given by its law $p$ on the subsets of $V\times W$, supported on matchings of $E$; $\mathbb E$ and $\Pr$ are finite sums over that law.
--
--   Differences from the source:
--   - encoding: a bipartite graph and vectors indexed by its edges → an edge set E : Finset (V × W) for finite V, W; vectors V × W → ℝ, the polytope's points vanishing off E; reason: a vector on E is the same as a vector on V × W vanishing off E
--   - encoding: a random matching M with E[1_M] and Pr(Z ≥ τµ) → its law p : Finset (V × W) → ℝ (IsRandomMatching E p), with expect and prob as finite sums; reason: every quantity in the statement depends only on the law of M, a distribution on a finite set
--   - encoding: coefficients α_e ∈ [0, 1] for the edges e → α : V × W → ℝ with values in [0, 1]; reason: M ⊆ E, so values off E do not enter Z; every α on E extends by 0
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 29, Lemma 30 ([CVZ11, Theorem 1.1])

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_LocalEdit

namespace GraphSimOT.Gaps

/-- Lemma 30 (App. D.2, p. 29; [CVZ11, Theorem 1.1]): for `q` in the bipartite matching
polytope and `γ ∈ (0, 1/2]` there is a random matching `M` with `E[1_M] = (1 − γ) q` such that
for every linear statistic `Z = ∑_e α_e 1[e ∈ M]` with `α_e ∈ [0, 1]`, every `µ ≥ E[Z]` with
`µ > 0` and every `τ ≥ 2`, `Pr(Z ≥ τµ) ≤ exp(−µγ(2τ − 3)/20)`. -/
theorem lemma_30 {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (E : Finset (V × W)) (q : V × W → ℝ) (hq : q ∈ matchingPolytope E)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) :
    ∃ p : Finset (V × W) → ℝ, IsRandomMatching E p ∧
      (∀ e, expect p (fun M => indic M e) = (1 - γ) * q e) ∧
      ∀ α : V × W → ℝ, (∀ e, 0 ≤ α e ∧ α e ≤ 1) →
        ∀ μ : ℝ, expect p (linStat α) ≤ μ → 0 < μ →
        ∀ τ : ℝ, 2 ≤ τ →
          prob p (fun M => τ * μ ≤ linStat α M) ≤ Real.exp (-(μ * γ * (2 * τ - 3)) / 20) := by sorry

end GraphSimOT.Gaps
