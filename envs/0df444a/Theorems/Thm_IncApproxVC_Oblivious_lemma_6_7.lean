-- Prove2me | Theorems.Thm_IncApproxVC_Oblivious_lemma_6_7
-- name    : IncApproxVC.Oblivious.lemma_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:44:00.067102+00:00
-- url     : https://prove2.me/theorems/4c728302-0c89-4c22-a4b8-f9154f39a319
-- title:
--   Lemma 6.7 — an $s^+$-rooted cut of $G_{\mathrm{split}}$ maps back to $(L,N^+_G(L),\text{rest})$ with $|S|\le|\partial^+(S')|$ and $\mathrm{vol}^+_G(L)\le\mathrm{vol}^+_{G_{\mathrm{split}}}(S')$
-- statement:
--   Let $G=(V,E)$ be a simple directed graph with split graph $G_{\mathrm{split}}$, and fix a root $s\in V$. For every $s^+$-rooted cut $(S',T')$ of $G_{\mathrm{split}}$, the triple
--   $$L=\{v\in V\mid v^-,v^+\in S'\}\cup\{s\},\qquad S=N^+_G(L),\qquad R=V\setminus(L\cup S)$$
--   is a partition of $V$ with $s\in L$, $E_G(L,R)=\emptyset$,
--   $$|S|\ \le\ |\partial^+_{G_{\mathrm{split}}}(S')|\qquad\text{and}\qquad \mathrm{vol}^+_G(L)\ \le\ \mathrm{vol}^+_{G_{\mathrm{split}}}(S').$$
--   Under the volume condition of Lemma 6.6 the right side is then nonempty and $(L,S,R)$ is an $s$-rooted separation triple; the page states that consequence as a pointer to Lemma 6.6.
--
--   Differences from the source:
--   - reading: In particular, under the correct volume conditions, Lemma 6.6 shows that (L, S, R) is an s-rooted separating triple. → not stated; reason: a pointer to Lemma 6.6 with unspecified conditions, not a separate claim; Lemma 6.6 is its own milestone
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 22, Lemma 6.7

import Mathlib
import Definitions.Def_IncApproxVC_Oblivious_Digraph
import Definitions.Def_IncApproxVC_Oblivious_VertexConnectivity
import Definitions.Def_IncApproxVC_Oblivious_Cuts

namespace IncApproxVC.Oblivious

/-- **Lemma 6.7** (mapping rooted cuts from the split graph to the original graph), p. 22. For every
`s⁺`-rooted cut `(S′, T′)` of `G_split`, the triple `L = {v ∈ V | v⁻, v⁺ ∈ S′} ∪ {s}`,
`S = N⁺_G(L)`, `R = V \ (L ∪ S)` is a partition of `V` with `s ∈ L`, `E_G(L, R) = ∅`,
`|S| ≤ |∂⁺_{G_split}(S′)|` and `vol⁺_G(L) ≤ vol⁺_{G_split}(S′)`. -/
theorem lemma_6_7 {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) (hG : G.Loopless)
    (s : V) (S' T' : Finset (V × Bool)) (hcut : Digraph.IsEdgeCut S' T')
    (hs : Digraph.plus s ∈ S') :
    Digraph.IsPartition3
        ((Finset.univ.filter fun v => Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') ∪ {s})
        (G.outNbhd ((Finset.univ.filter fun v =>
          Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') ∪ {s}))
        (Finset.univ \ (((Finset.univ.filter fun v =>
            Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') ∪ {s}) ∪
          G.outNbhd ((Finset.univ.filter fun v =>
            Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') ∪ {s}))) ∧
      s ∈ (Finset.univ.filter fun v => Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') ∪ {s} ∧
      G.edgesBetween
          ((Finset.univ.filter fun v => Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') ∪ {s})
          (Finset.univ \ (((Finset.univ.filter fun v =>
              Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') ∪ {s}) ∪
            G.outNbhd ((Finset.univ.filter fun v =>
              Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') ∪ {s}))) = ∅ ∧
      (G.outNbhd ((Finset.univ.filter fun v =>
          Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') ∪ {s})).card ≤
        (G.split.outBoundary S').card ∧
      G.vol ((Finset.univ.filter fun v => Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') ∪ {s}) ≤
        G.split.vol S' := by sorry

end IncApproxVC.Oblivious
