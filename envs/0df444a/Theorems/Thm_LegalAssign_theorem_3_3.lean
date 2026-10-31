-- Prove2me | Theorems.Thm_LegalAssign_theorem_3_3
-- name    : LegalAssign.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:26.510201+00:00
-- url     : https://prove2.me/theorems/2abc5541-4a58-4340-9bb8-2dc2eab5b6c3
-- title:
--   Theorem 3.3 — existence and uniqueness of the legal set (Morrill)
-- statement:
--   Let $(G,<,q)$ be an instance of the stable assignment problem. There is a unique set $\mathcal L\subseteq\mathcal M(G,q)$ with the legal property.
--
--   The theorem is due to Morrill. It makes $\mathcal L(G,<,q)$, the set of legal assignments of an instance, well defined.
--
--   Differences from the source:
--   - encoding: <_v is a strict ordering of the neighbours of v in G → prefA a and prefB b are strict total orders on the whole other side; reason: only comparisons among neighbours ever enter, and every strict order on the neighbours extends to the whole side
--   - encoding: G is a bipartite graph, finite throughout the paper → Fintype A, Fintype B, E : Finset (A × B), assignments are Finsets of pairs; reason: Lean convention; the same instances
--   - reading: q = {q_b} ∈ ℕ^B, with no statement on whether this ℕ contains 0 → q : B → ℕ, so q_b = 0 is allowed; reason: the source does not settle it, and the Lean statement covers positive quotas and quota 0 alike
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, Theorem 3.3, p.8 (due to Morrill [27])

import Mathlib
import Definitions.Def_LegalAssign_Instance

namespace LegalAssign

/-- Theorem 3.3 (arXiv:1809.08506v2, p.8, due to Morrill [27]): there is a unique `𝓛 ⊆ 𝓜(G, q)` with the
legal property. -/
theorem theorem_3_3 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) :
    ∃! L : Set (Finset (A × B)), L ⊆ G.assignments ∧ G.HasLegalProperty L := by sorry

end LegalAssign
