-- Prove2me | Theorems.Thm_MultipleUnicast_Counterexample_balanced_orientation
-- name    : MultipleUnicast.Counterexample.balanced_orientation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:21:57.578823+00:00
-- url     : https://prove2.me/theorems/8e70cd2b-910e-4e63-baf7-27f41c4d8ecf
-- title:
--   Section 4, unnumbered degree identities — full candidate orientation
-- statement:
--   For the exact Appendix A data, the lexicographic incidence list contains 910 distinct edges, the vertex list is a permutation of all 182 labels, $|R|=175$, and $C,J$ are disjoint nine-element subsets of $R$. Thus $|B|=157$ and $|E(G)|=735$. Orient physical edges earlier to later and every deleted edge later to earlier. At every vertex $v$,
--   $$d^-(v)=d^+(v)=5,\qquad d_C^+(v)=d_J^-(v).$$
--   These degrees refer to all 910 candidate edges. The finite indexing facts are included as conclusions alongside the identities they make meaningful. They supply the data checks used by the local construction.
--
--   Differences from the source:
--   - encoding: the source labels vertices and candidate edges by integers and sessions by B → Fin 182 and Fin 910 labels, with a fixed equivalence B ≃ Fin (card B) where needed; reason: the same finite objects and source/sink order are retained
-- source:
--   Mark Braverman, Zhongtian He, STOC 2027 submission #286 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/286.pdf, §4, unnumbered degree identities, PDF p. 11 / printed p. 10; indexing facts in §3, PDF p. 6 / printed p. 5 and Appendix A, PDF pp. 14–15 / printed pp. 13–14

import Definitions.Def_MultipleUnicast_Counterexample_Protocol

set_option maxRecDepth 2048

namespace MultipleUnicast.Counterexample

/-- §4 degree identities, with the finite indexing facts from §3 and Appendix A. -/
theorem balanced_orientation :
    incidenceList.length = 910 ∧ incidenceList.Nodup ∧ Function.Injective edgePair ∧
    processingOrder.Perm (List.finRange 182) ∧
    deleted.card = 175 ∧ C.card = 9 ∧ J.card = 9 ∧
    C ⊆ deleted ∧ J ⊆ deleted ∧ Disjoint C J ∧
    B.card = 157 ∧ physical.card = 735 ∧
    ∀ v : Vertex,
      inDegree Finset.univ v = 5 ∧ outDegree Finset.univ v = 5 ∧
      outDegree C v = inDegree J v := by sorry

end MultipleUnicast.Counterexample
