-- Prove2me | Theorems.Thm_IncApproxVC_Oblivious_lemma_6_3
-- name    : IncApproxVC.Oblivious.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:43:29.764789+00:00
-- url     : https://prove2.me/theorems/c415158d-9ab4-40d4-86e0-27cf89f17f6a
-- title:
--   Lemma 6.3 — $|N^+_G(L)|\le|\partial^+_{G_{\mathrm{split}}}(S)|$ for $L=\{v: v^-,v^+\in S\}$
-- statement:
--   Let $G=(V,E)$ be a simple directed graph and $G_{\mathrm{split}}=(V',E')$ its split graph. For every set $S\subseteq V'$ and
--   $$L=\{v\in V\mid v^-,v^+\in S\}$$
--   we have
--   $$|N^+_G(L)|\ \le\ |\partial^+_{G_{\mathrm{split}}}(S)|.$$
--   This is the basic inequality translating edge cuts of the split graph back into vertex cuts of $G$.
--
--   Differences from the source: none.
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 20, Lemma 6.3

import Mathlib
import Definitions.Def_IncApproxVC_Oblivious_Digraph
import Definitions.Def_IncApproxVC_Oblivious_Cuts

namespace IncApproxVC.Oblivious

/-- **Lemma 6.3**, p. 20. For a graph `G` with split graph `G_split`, every set `S` of vertices of
`G_split` and `L = {v ∈ V | v⁻, v⁺ ∈ S}`: `|N⁺_G(L)| ≤ |∂⁺_{G_split}(S)|`. -/
theorem lemma_6_3 {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) (hG : G.Loopless)
    (S : Finset (V × Bool)) :
    (G.outNbhd (Finset.univ.filter fun v => Digraph.minus v ∈ S ∧ Digraph.plus v ∈ S)).card ≤
      (G.split.outBoundary S).card := by sorry

end IncApproxVC.Oblivious
