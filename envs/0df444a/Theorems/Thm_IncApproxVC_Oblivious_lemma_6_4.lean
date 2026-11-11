-- Prove2me | Theorems.Thm_IncApproxVC_Oblivious_lemma_6_4
-- name    : IncApproxVC.Oblivious.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:43:39.795227+00:00
-- url     : https://prove2.me/theorems/808e9984-35cc-4717-963e-e6e282824ab0
-- title:
--   Lemma 6.4 — $s$–$t$ vertex cuts of $G$ and $s^+$–$t^-$ cuts of $G_{\mathrm{split}}$, in both directions
-- statement:
--   Let $G=(V,E)$ be a simple directed graph with split graph $G_{\mathrm{split}}$, and let $s,t\in V$ with $t\notin N^+_G[s]$.
--   1. For every $s$–$t$ separation triple $(L,S,R)$ of $G$, the pair
--   $$S'=\{v^-,v^+\mid v\in L\}\cup\{v^-\mid v\in S\},\qquad T'=\{v^-,v^+\mid v\in R\}\cup\{v^+\mid v\in S\}$$
--   is an $s^+$–$t^-$ cut of $G_{\mathrm{split}}$ with $|\partial^+_{G_{\mathrm{split}}}(S')|=|S|$.
--   2. For every $s^+$–$t^-$ cut $(S',T')$ of $G_{\mathrm{split}}$, the triple
--   $$L=\{s\}\cup\{v\in V\mid v^-,v^+\in S'\}\setminus N^-_G(t),\qquad S=N^+_G(L),\qquad R=V\setminus(L\cup S)$$
--   is an $s$–$t$ separation triple of $G$ with $|S|\le|\partial^+_{G_{\mathrm{split}}}(S')|$.
--
--   Together these give that the minimum $s$–$t$ vertex cut of $G$ equals the minimum $s^+$–$t^-$ edge cut of $G_{\mathrm{split}}$.
--
--   **Formalization Note.** $L$ is computed as $(\{s\}\cup\{v\mid v^-,v^+\in S'\})\setminus N^-_G(t)$. Since $t\notin N^+_G[s]$ gives $s\notin N^-_G(t)$, this is the same set as $\{s\}\cup(\{v\mid v^-,v^+\in S'\}\setminus N^-_G(t))$.
--
--   Differences from the source:
--   - encoding: L = {s} ∪ {v ∈ V | v⁻, v⁺ ∈ S′} \ N⁻_G(t) → ({s} ∪ {v | v⁻, v⁺ ∈ S′}) \ N⁻_G(t); reason: both groupings give the same set because s ∉ N⁻_G(t) when t ∉ N⁺_G[s]
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 20, Lemma 6.4

import Mathlib
import Definitions.Def_IncApproxVC_Oblivious_Digraph
import Definitions.Def_IncApproxVC_Oblivious_VertexConnectivity
import Definitions.Def_IncApproxVC_Oblivious_Cuts

namespace IncApproxVC.Oblivious

/-- **Lemma 6.4** (`s⁺–t⁻` cuts in split graphs), p. 20. Let `s, t` be vertices of `G` with
`t ∉ N⁺_G[s]`.
1. For every `s–t` separation triple `(L, S, R)` of `G`, the pair
   `S′ = {v⁻, v⁺ | v ∈ L} ∪ {v⁻ | v ∈ S}`, `T′ = {v⁻, v⁺ | v ∈ R} ∪ {v⁺ | v ∈ S}` is an `s⁺–t⁻`
   cut of `G_split` with `|∂⁺_{G_split}(S′)| = |S|`.
2. For every `s⁺–t⁻` cut `(S′, T′)` of `G_split`, the triple
   `L = {s} ∪ {v ∈ V | v⁻, v⁺ ∈ S′} \ N⁻_G(t)`, `S = N⁺_G(L)`, `R = V \ (L ∪ S)` is an `s–t`
   separation triple of `G` with `|S| ≤ |∂⁺_{G_split}(S′)|`. -/
theorem lemma_6_4 {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) (hG : G.Loopless)
    (s t : V) (hst : t ∉ G.closedOutNbhd {s}) :
    (∀ L S R : Finset V, G.IsSeparationTriple L S R → s ∈ L → t ∈ R →
        Digraph.IsEdgeCut (L.image Digraph.minus ∪ L.image Digraph.plus ∪ S.image Digraph.minus)
            (R.image Digraph.minus ∪ R.image Digraph.plus ∪ S.image Digraph.plus) ∧
          Digraph.plus s ∈
            L.image Digraph.minus ∪ L.image Digraph.plus ∪ S.image Digraph.minus ∧
          Digraph.minus t ∈
            R.image Digraph.minus ∪ R.image Digraph.plus ∪ S.image Digraph.plus ∧
          (G.split.outBoundary
            (L.image Digraph.minus ∪ L.image Digraph.plus ∪ S.image Digraph.minus)).card =
            S.card) ∧
      (∀ S' T' : Finset (V × Bool), Digraph.IsEdgeCut S' T' → Digraph.plus s ∈ S' →
        Digraph.minus t ∈ T' →
        G.IsSeparationTriple
            (insert s (Finset.univ.filter fun v => Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') \
              G.inNbhd {t})
            (G.outNbhd (insert s (Finset.univ.filter fun v =>
              Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') \ G.inNbhd {t}))
            (Finset.univ \
              ((insert s (Finset.univ.filter fun v =>
                  Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') \ G.inNbhd {t}) ∪
                G.outNbhd (insert s (Finset.univ.filter fun v =>
                  Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') \ G.inNbhd {t}))) ∧
          s ∈ insert s (Finset.univ.filter fun v =>
            Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') \ G.inNbhd {t} ∧
          t ∈ Finset.univ \
              ((insert s (Finset.univ.filter fun v =>
                  Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') \ G.inNbhd {t}) ∪
                G.outNbhd (insert s (Finset.univ.filter fun v =>
                  Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') \ G.inNbhd {t})) ∧
          (G.outNbhd (insert s (Finset.univ.filter fun v =>
              Digraph.minus v ∈ S' ∧ Digraph.plus v ∈ S') \ G.inNbhd {t})).card ≤
            (G.split.outBoundary S').card) := by sorry

end IncApproxVC.Oblivious
