-- Prove2me | Theorems.Thm_MinBisectFPT_lemma_4_1
-- name    : MinBisectFPT.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:34.8267+00:00
-- url     : https://prove2.me/theorems/0bc6282c-f684-4bd4-96e9-540377ba56e1
-- title:
--   Lemma 4.1 — the subtree graph splits into the bag graph and the children
-- statement:
--   Under the standing assumptions of §4, let $t$ have children $c_1,\dots,c_r$. Then:
--
--   1. $\beta(t),\alpha(c_1),\dots,\alpha(c_r)$ partition $\gamma(t)$, and no edge joins distinct child components.
--   2. For each $i$, $N_G(\alpha(c_i))=\sigma(c_i)$ is a nonempty subset of $\beta(t)$.
--   3. $B_t,G_{c_1},\dots,G_{c_r}$ are subgraphs of $G_t$ with pairwise disjoint edge sets whose union is $E(G_t)$.
--
--   Differences from the source:
--   - encoding: children $c_1,\dots,c_r$ → the set `D.children t`; reason: same nodes; $r=0$ needs no case
--   - reading: "no edge joins" → no edge of $G$; reason: the proof shows the statement in $G$, and it implies the statement in $G_t$
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 4.1, pp.10–11

import Mathlib
import Definitions.Def_MinBisectFPT_NodeCtx

open scoped Classical

namespace MinBisectFPT

/-- **Lemma 4.1.** Anand, Kipouridis, Węgrzycki, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 4.1, pp.10–11, with its standing assumptions (`NodeCtx`, p.10). The children
are the set `D.children t`, so `r = 0` needs no case. "No edge" in (i) is in `G`. -/
theorem lemma_4_1 {n : ℕ} (ctx : NodeCtx n) :
    (ctx.β ∪ (ctx.D.children ctx.t).biUnion ctx.D.component = ctx.γ ∧
      (∀ c ∈ ctx.D.children ctx.t, Disjoint ctx.β (ctx.D.component c)) ∧
      (∀ c ∈ ctx.D.children ctx.t, ∀ c' ∈ ctx.D.children ctx.t, c ≠ c' →
        Disjoint (ctx.D.component c) (ctx.D.component c') ∧
          ∀ u ∈ ctx.D.component c, ∀ v ∈ ctx.D.component c', ¬ctx.G.Adj u v)) ∧
    (∀ c ∈ ctx.D.children ctx.t, nbr ctx.G (ctx.D.component c) = ctx.D.adhesion c ∧
      (ctx.D.adhesion c).Nonempty ∧ ctx.D.adhesion c ⊆ ctx.β) ∧
    (ctx.B ≤ ctx.H ∧
      (∀ c ∈ ctx.D.children ctx.t, subtreeGraph ctx.G ctx.D c ≤ ctx.H ∧
        Disjoint ctx.B.edgeSet (subtreeGraph ctx.G ctx.D c).edgeSet) ∧
      (∀ c ∈ ctx.D.children ctx.t, ∀ c' ∈ ctx.D.children ctx.t, c ≠ c' →
        Disjoint (subtreeGraph ctx.G ctx.D c).edgeSet (subtreeGraph ctx.G ctx.D c').edgeSet) ∧
      ctx.H.edgeSet = ctx.B.edgeSet ∪
        ⋃ c ∈ ctx.D.children ctx.t, (subtreeGraph ctx.G ctx.D c).edgeSet) := by sorry

end MinBisectFPT
