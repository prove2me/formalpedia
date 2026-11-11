-- Prove2me | Theorems.Thm_ImprovedSteinerForest_Main_lemma_A_1
-- name    : ImprovedSteinerForest.Main.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:28:06.918209+00:00
-- url     : https://prove2.me/theorems/b0ec3b9d-559d-4254-9e68-32dc6dd665d5
-- title:
--   Lemma A.1 — for fixed t, an exact minimum connector of demand pairs with ≤ t endpoints, and a minimum Steiner tree on ≤ t vertices, in polynomial time
-- statement:
--   Fix a positive integer $t$.
--
--   1. There is a deterministic polynomial-time algorithm that, given a Steiner Forest instance whose demand pairs have at most $t$ distinct endpoints, outputs a **connector** of minimum cost, i.e. an edge set $F$ of input edges that is feasible with
--   $$c(F)=\mathrm{opt},$$
--   if one exists, and reports that none exists otherwise.
--   2. In particular, there is a deterministic polynomial-time algorithm that, given an input graph and a specified set $T$ of at most $t$ vertices, finds a minimum Steiner tree on $T$ (a tree of input edges connecting $T$ whose cost is at most that of any edge set connecting $T$), or reports that $T$ cannot be connected.
--
--   The algorithm prices the purchases of §3.2, whose bought pairs have at most $2v\le 80$ endpoints, and the components of the rounding relaxation.
--
--   **Formalization Note.** One machine per value of $t$. A found connector is output as the bit `1` followed by its edge-set code, and "none exists" as the single bit `0`. For part 2 the machine reads the instance code (its demand list is ignored) followed by the code of $T$.
--
--   Differences from the source:
--   - generalization: finite undirected network → multigraph edge list on `Fin n` with loops, parallel edges and repeated labelled pairs; reason: contraction produces multigraphs (p. 13); a simple network is a special case.
--   - encoding: "finds a connector … or reports that none exists" → output `true :: encEdgeSet I F` with `F` feasible and `c(F) = opt`, or `[false]` on infeasible inputs; reason: a two-case output must be distinguishable.
--   - encoding: "minimum Steiner tree on a specified set" → `IsSteinerTree F T` (a forest connecting `T`, each edge in the component of `T`) with cost at most that of every edge set connecting `T`, on input `encInst I ++ encVertexSet I T`; reason: the set is part of the input.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Improved Steiner Forest Approximation via Cut Spaces, STOC 2027 submission (manuscript sha256 b2bf022d…0444), p. 42, Lemma A.1

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_ImprovedSteinerForest_Main_Instance
import Definitions.Def_ImprovedSteinerForest_Main_Encoding
open QAlgorithms.Complexity

namespace ImprovedSteinerForest.Main

/-- Lemma A.1 (p. 42): for each fixed positive integer `t`, a deterministic polynomial-time
algorithm, given demand pairs with at most `t` distinct endpoints, finds a connector of input edges
of minimum cost or reports that none exists; in particular it finds a minimum Steiner tree on any
specified set of at most `t` vertices. -/
theorem lemma_A_1 (t : ℕ) (ht : 0 < t) :
    (∃ M : Str → Str, PolyTimeComputable M ∧
      ∀ I : Instance, I.endpoints.card ≤ t →
        (I.IsFeasibleInst → ∃ F : Finset I.Edge,
          M (encInst I) = true :: encEdgeSet I F ∧ I.Feasible F ∧ I.cost F = I.opt) ∧
        (¬ I.IsFeasibleInst → M (encInst I) = [false])) ∧
    (∃ M : Str → Str, PolyTimeComputable M ∧
      ∀ I : Instance, ∀ T : Finset (Fin I.n), T.card ≤ t →
        (I.ConnectsSet Finset.univ T → ∃ F : Finset I.Edge,
          M (encInst I ++ encVertexSet I T) = true :: encEdgeSet I F ∧ I.IsSteinerTree F T ∧
            ∀ F' : Finset I.Edge, I.ConnectsSet F' T → I.cost F ≤ I.cost F') ∧
        (¬ I.ConnectsSet Finset.univ T → M (encInst I ++ encVertexSet I T) = [false])) := by sorry

end ImprovedSteinerForest.Main
