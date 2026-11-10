-- Prove2me | Theorems.Thm_NogoodColoring1137_Main_two_list_counting
-- name    : NogoodColoring1137.Main.two_list_counting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T17:03:28.912009+00:00
-- url     : https://prove2.me/theorems/8149c178-fa80-452c-89a0-52c2a37b54a5
-- title:
--   Lemma 6.2 — Exact two-list counting in squared-logarithm time
-- statement:
--   For any $n$-vertex graph of diameter at most two and lists of size at most two from three fixed colors, the defined recursion returns the exact fixed-name count. A uniform finite program computes it for positive global $A,C$:
--   $$\operatorname{TwoListCount}(G,L)=|\mathcal C(G,L)|,\qquad t\le A\exp(C[\ln(n+1)]^2).$$
--   With $s$ the original number of two-list vertices, the recursion has at most $(s+1)^{\lceil\log_{6/5}(s+1)\rceil+1}$ leaves. Empty lists yield zero; the empty graph has one coloring. Common-list bipartite branches count isolated components. Counts are binary and exact arithmetic is charged.
--
--   This supplies the counting subroutine for every box. **Formalization Note** The leaf bound unrolls (10), retaining $5/6$ and $6/5$. Local certificates and finite parity closure implement the source recursion without a solution or counting oracle.
--
--   Differences from the source:
--   - encoding: deterministic algorithms on explicit finite inputs → actual finite multitape bit-machine runs with binary integer and explicit output encodings; reason: the source fixes no bit layout; uniform programs and positive constants precede every input
--   - encoding: the recursion described in §6 → CountRec with n fuel, simultaneous singleton rounds and finite parity closure; reason: each recursive edge fixes a two-list vertex; color bits and parity states bound closure rounds without changing the result
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), Lemma 6.2, p.20, equation (10)

import Definitions.Def_NogoodColoring1137_Main_TwoListRecursion

namespace NogoodColoring1137.Main

/-- Lemma 6.2, p.20: exact count, including empty lists and all small graphs. -/
theorem two_list_counting :
    ∃ (P : IntMul.MultitapeTM) (A C : ℝ), 0 < A ∧ 0 < C ∧
      ∀ n (G : SimpleGraph (Fin n)) (adj : DecidableRel G.Adj) (L : Lists n),
        DiameterTwo G → (∀ v, (L v).card ≤ 2) →
        @TwoListCount n G adj L = (@Solutions n G adj L).card ∧
        (@CountRec n G adj n L).2 ≤ LeafBound (TwoVertices L).card ∧
        Runs P (@EncodeInstance n G adj L) (EncodeNat (@TwoListCount n G adj L))
          (LogTime 2 A C n) := by sorry

end NogoodColoring1137.Main
