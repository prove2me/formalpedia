-- Prove2me | Theorems.Thm_OAI_UniqueGamesTheorem_theorem11
-- name    : OAI.UniqueGamesTheorem.theorem11
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:36.622277+00:00
-- url     : https://prove2.me/theorems/7add89f2-2a6b-4e11-aff4-23640077659e
-- statement:
--   The theorem states that, for any real numbers ε and δ with 0<ε<1/2 and 0<δ<1/2, there exists a BinaryGapReduction ε δ, a polynomial-time reduction from satisfiability of binary-encoded 3-clause formulas to translation Unique Games. The source language consists of bit-strings that decode, under a canonical self-delimiting encoding with sparse variable names, to a conjunction of clauses of three literals (repeats allowed) that has a satisfying assignment. A reduction consists of the following data, all fixed before any input is chosen. There is an alphabet size q≥2, a dimension s≥1, and an equivalence between the q labels and the vectors in F₂^s. There is a map construct sending each input bit-list to a Unique Games instance over q labels, whose constraints form a nonempty list (so multiplicities are kept), each given by a source vertex, a target vertex and a permutation of the labels with explicit inverse table. Every constructed instance is simple bipartite: vertices are split into two sides, every constraint goes from the false side to the true side, and no two distinct constraint entries share the same (source, target) pair. Every constraint permutation is a translation, meaning it adds some fixed vector in F₂^s to the coordinates of each label. The map construct is computed by a Mathlib Turing machine (TM2) in polynomial time on the raw input bit length, with output the bit encoding of the instance, and every tape alphabet of that machine is finite. Completeness: if the input formula is satisfiable, some labeling of the vertices satisfies at least a 1−ε fraction of the constraints. Soundness: if the input is not a satisfiable formula (including any string that fails to decode), every labeling satisfies at most a δ fraction of the constraints. The alphabet and machine depend only on ε and δ. The theorem is stated with its proof admitted (sorry).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/UniqueGamesTheorem.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/UniqueGamesTheorem.lean; bytes 8310..8748
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_UniqueGamesTheorem

namespace OAI

namespace UniqueGamesTheorem

/-- For every fixed pair of errors in `(0, 1/2)`, binary 3SAT reduces in
polynomial time to translation Unique Games with completeness at least `1 - ε`
and soundness at most `δ`. The alphabet and machine depend only on the errors. -/
theorem theorem11 (ε δ : ℝ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    Nonempty (Explicit.MachineOutputContract.BinaryGapReduction ε δ) := by
  sorry

end UniqueGamesTheorem
end OAI
