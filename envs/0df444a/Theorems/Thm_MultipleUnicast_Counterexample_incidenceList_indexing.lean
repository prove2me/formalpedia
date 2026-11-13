-- Prove2me | Theorems.Thm_MultipleUnicast_Counterexample_incidenceList_indexing
-- name    : MultipleUnicast.Counterexample.incidenceList_indexing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T09:18:11.348983+00:00
-- url     : https://prove2.me/theorems/6c2fc3b1-1798-4317-a5fb-0b2f5455a6e9
-- title:
--   §4 — the 910 candidate edges of PG(2,9) are indexed without repetition
-- statement:
--   The list `incidenceList` of incident (point, line) pairs of $PG(2,9)$, in lexicographic order (increasing point, then increasing line, with incidence tested by the dot product of the normalized triples), has length $910$ and no repeated entry, and the indexing `edgePair : Fin 910 → Fin 91 × Fin 91` reading entry $q$ of that list is injective.
--
--   This is the first three conjuncts of `MultipleUnicast.Counterexample.balanced_orientation` (mission *The Multiple Unicast Conjecture is False*, §4, p. 9: "Number the candidate edges by $e_{10i+r} = \{i, 91 + j_{i,r}\}$"), published on its own so that the proof of that milestone splits into pieces that fit the verifier's time limit. All objects are those of the bundle `Def_MultipleUnicast_Counterexample_Graph`.
-- source:
--   The Multiple Unicast Conjecture is False: Causal network coding beats fractional routing (STOC 2027 submission 286), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/286.pdf, p. 9, the candidate-edge numbering e_{10i+r} of §4 (910 distinct incidences of PG(2,9))

import Mathlib
import Definitions.Def_MultipleUnicast_Counterexample_Graph

namespace MultipleUnicast.Counterexample

theorem incidenceList_indexing :
    incidenceList.length = 910 ∧ incidenceList.Nodup ∧ Function.Injective edgePair := by
  sorry

end MultipleUnicast.Counterexample
