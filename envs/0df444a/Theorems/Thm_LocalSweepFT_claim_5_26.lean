-- Prove2me | Theorems.Thm_LocalSweepFT_claim_5_26
-- name    : LocalSweepFT.claim_5_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:39:54.736094+00:00
-- url     : https://prove2.me/theorems/d6b7b8ea-c7fe-4969-9ed2-d71a52d95c54
-- title:
--   Claim 5.26 — a slice's poles are bounded by those of a fork-connected family of predecessor slices
-- statement:
--   Let $(G,T)$ be a space–time graph whose vertices carry points of $\mathbb R^d$, let $\mathrm{pre}_i$ be any choice of $L_i$-maximizing predecessors, let $K$ be a slice with $K\ne H_K$, and let $v_1,\dots,v_{d+1}$ be a pole selection for $K$. Then for some $k$ there are pairwise distinct slices $K_0,\dots,K_k$ with pole selections $(v^i_j)_{i}$ and forks $F_1,\dots,F_k$ such that
--   1. every $\mathrm{pre}_i(v_i)$ is among the selected poles of $K_0,\dots,K_k$;
--   2. the graph on $K_0,\dots,K_k$ in which $K_j,K_{j'}$ are adjacent iff some fork $F_m$ meets the selected poles of both is connected;
--   3. $$\sum_{j=0}^{k}\sum_{i=1}^{d+1}L_i(v^i_j)+\sum_{m=1}^{k}\mathrm{Size}(F_m)\ge\sum_{i=1}^{d+1}L_i(\mathrm{pre}_i(v_i)).$$
--
--   This recursion builds the explanation trees whose counting gives the $p^{\Omega(n)}$ bound.
--
--   Differences from the source:
--   - encoding: pre_i(u) := arg max_{v ∈ pre(u)} L_i(v) → any choice of maximizers (IsPreSelection); reason: the arg max may not be unique; every choice is covered
--   - reading: a fork "intersects both K_i's and K_j's selected poles" → an endpoint of the fork is a selected pole of K_j and an endpoint is a selected pole of K_{j′}; reason: the fork is a two-element set
--   - encoding: "k forks F₁, …, F_k with pole selections for them" → k forks, without pole selections; reason: the conclusion uses only Size(F_m), which does not depend on a pole selection
--   - reading: history: vertices of time ≤ T(u) connected to u by a path of arrows (Def 5.21) → paths inside the vertices of time ≤ T(u); reason: the reading under which Claims 5.22 and 5.24, used in the proof, go through
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 5.26, pp.49–50

import Mathlib
import Definitions.Def_LocalSweepFT_SpaceTimeGraph

namespace LocalSweepFT

/-- Claim 5.26, pp.49–50 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). Let `(G, T)` be a space–time graph whose vertices
are associated with points of `ℝ^d`, `K` a slice with `K ≠ H_K`, and `v_1, …, v_{d+1}` a pole
selection for `K`. Then for some integer `k` there are `k + 1` slices `K_0, …, K_k` with pole
selections `(v^i_j)_i` and `k` forks `F_1, …, F_k` such that
1. every `pre_i(v_i)` is among the selected poles of `K_0, …, K_k`;
2. the graph on `K_0, …, K_k` in which `K_j`, `K_{j′}` are adjacent iff some fork `F_m` meets the
   selected poles of both is connected;
3. `Σ_{j=0}^k Σ_{i=1}^{d+1} L_i(v^i_j) + Σ_{m=1}^k Size(F_m) ≥ Σ_{i=1}^{d+1} L_i(pre_i(v_i))`.

**Formalization Note.** The predecessors `pre_i` are any choice of maximizers (`IsPreSelection`);
the slices `K_j` are given by representatives `rep j` (`K_j = slice (rep j)`), and
the `k + 1` slices are pairwise distinct. The slice `K` is the
slice of `u`. -/
theorem claim_5_26 (d : ℕ) {V : Type} (G : SpaceTimeGraph V) (pos : V → (Fin d → ℝ))
    (preSel : V → Fin (d + 1) → V) (hpre : IsPreSelection G pos preSel) (u : V)
    (hK : G.slice u ≠ G.hist u) (vp : Fin (d + 1) → V) (hvp : ∀ i, vp i ∈ G.slice u) :
    ∃ (k : ℕ) (rep : Fin (k + 1) → V) (poles : Fin (k + 1) → Fin (d + 1) → V)
      (fork : Fin k → V × V),
      Function.Injective (fun j => G.slice (rep j)) ∧
      (∀ j i, poles j i ∈ G.slice (rep j)) ∧
      (∀ m, G.F.Adj (fork m).1 (fork m).2) ∧
      (∀ i, ∃ j i', poles j i' = preSel (vp i) i) ∧
      (SimpleGraph.fromRel (fun j j' : Fin (k + 1) => ∃ m,
        ((fork m).1 ∈ Set.range (poles j) ∨ (fork m).2 ∈ Set.range (poles j)) ∧
        ((fork m).1 ∈ Set.range (poles j') ∨ (fork m).2 ∈ Set.range (poles j')))).Connected ∧
      ∑ i, potR i (pos (preSel (vp i) i)) ≤
        ∑ j, ∑ i, potR i (pos (poles j i)) + ∑ m, forkSize pos (fork m).1 (fork m).2 := by sorry

end LocalSweepFT
