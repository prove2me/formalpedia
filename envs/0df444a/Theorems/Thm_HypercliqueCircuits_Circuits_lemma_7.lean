-- Prove2me | Theorems.Thm_HypercliqueCircuits_Circuits_lemma_7
-- name    : HypercliqueCircuits.Circuits.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:35:59.786269+00:00
-- url     : https://prove2.me/theorems/f4318fa3-e5f3-4f8b-9cbb-143acebc5b07
-- title:
--   Lemma 7 — large biclique edge partition
-- statement:
--   For the source support graph with $q=2^B$, $B\ge16$, $d\ge0$ and $t=\lfloor d/B\rfloor$, there is a finite list of complete bipartite subgraphs $S\times J$ whose edges cover each edge of $G$ exactly once and contain no edge outside $G$. Every biclique satisfies
--
--   $$|S|,|J|\ge\ell,\qquad \ell=2^{(B-1)\lfloor(d-t)/B\rfloor}.$$
--
--   The shores need not be balanced, nor disjoint between bicliques. At $d=0$ the graph has one edge and $\ell=1$. The target concerns this particular computed graph and does not assume a suitable decomposition as input.
--
--   Differences from the source:
--   - encoding: q=2^B, n=q^d, t=floor(d/B) → rows indexed directly by q-ary digit vectors; reason: digit-vector indices have exactly q^d values; d=0 gives the singleton instance n=1
--   - encoding: disjoint union of biclique edge sets → a list of shore pairs, completeness and unique membership of each edge by list index; reason: equivalent finite edge partition; overlapping vertices and unequal shore sizes remain allowed
--   - generalization: the admissible induction parameters of the section → every B at least 16 and every d, with no epsilon or inductive circuit premise; reason: the graph and partition depend only on B,d and the exact threshold
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, Lemma 7, p.20 (PDF 21), proof completed p.21 (PDF 22).

import Definitions.Def_HypercliqueCircuits_Circuits_Transpose
import Definitions.Def_HypercliqueCircuits_Circuits_Machine

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits

/-- Lemma 7, printed p.20 / PDF 21. The exact floor/exponent is in bicliqueThreshold. -/
theorem lemma_7 (B d : ℕ) (hB : 16 ≤ B) :
    ∃ bs : List (Finset (Label (2^B) d) × Finset (Digits (2^B) d)),
      BicliquePartition B d bs := by sorry

end HypercliqueCircuits.Circuits
