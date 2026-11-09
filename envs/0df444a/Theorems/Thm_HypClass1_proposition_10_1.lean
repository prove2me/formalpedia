-- Prove2me | Theorems.Thm_HypClass1_proposition_10_1
-- name    : HypClass1.proposition_10_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:33:39.173202+00:00
-- url     : https://prove2.me/theorems/517f8bd4-0497-4922-a0e8-7d5cf4ec7a7e
-- title:
--   Proposition 10.1 — greedy recolouring into matchings through $x$
-- statement:
--   Let $G$ be a 3-graph on $[n]$, $x \in [n]$ a vertex, and $G = E \cup F_1 \cup \dots \cup F_t$ a partition such that
--   1. every edge of $E$ contains $x$;
--   2. each $F_i$ is a matching with $x \notin V(F_i)$;
--   3. $|E| > 3(t + \Delta_2(G))$.
--
--   Then there is a partition $G = F'_1 \cup \dots \cup F'_s$ of $G$ into matchings with $x \in V(F'_i)$ for every $i$.
--
--   This is the final absorption step: the reserved edges at the maximum-degree vertex absorb the few colour classes that miss it.
--
--   **Formalization Note** Partitions are families of pairwise disjoint parts with union $G$; the parts $E, F_i$ may be empty.
--
--   Differences from the source: none.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Proposition 10.1, p.57

import Mathlib
import Definitions.Def_HypClass1_K3
import Definitions.Def_HypClass1_maxCodeg
import Definitions.Def_HypClass1_IsMatching

namespace HypClass1

/-- **Proposition 10.1 (greedy recolouring).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Proposition 10.1, p.57:
"Let G be a 3-graph on n vertices such that the following holds. There exists a vertex x ∈ [n] and a
partition G = E ∪ F₁ ∪ … ∪ F_t such that
(i) Every edge e ∈ E contains the vertex x,
(ii) F_i is a matching and x ∉ V(F_i) for 1 ≤ i ≤ t,
(iii) |E| > 3(t + ∆₂(G)),
Then there exists a partition of G = F′₁ ∪ … ∪ F′_s into matchings such that x ∈ V(F′_i) for every
1 ≤ i ≤ s."

**Formalization Note.** A partition is a family of pairwise disjoint parts with union `G`; the parts
`E, F₁, …, F_t` may be empty. Each `F′_i` contains an edge through `x`, so it is non-empty. -/
theorem proposition_10_1 (n : ℕ) (G : Finset (Finset (Fin n))) (hG : G ⊆ K3 (Fin n)) (x : Fin n)
    (E : Finset (Finset (Fin n))) (t : ℕ) (F : Fin t → Finset (Finset (Fin n)))
    (hpart : E ∪ Finset.univ.biUnion F = G) (hEF : ∀ i, Disjoint E (F i))
    (hFF : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (hE : ∀ e ∈ E, x ∈ e) (hF : ∀ i, IsMatching (F i) ∧ x ∉ verts (F i))
    (hcard : E.card > 3 * (t + maxCodeg G)) :
    ∃ s : ℕ, ∃ F' : Fin s → Finset (Finset (Fin n)),
      Finset.univ.biUnion F' = G ∧ (∀ i j, i ≠ j → Disjoint (F' i) (F' j)) ∧
      ∀ i, IsMatching (F' i) ∧ x ∈ verts (F' i) := by sorry

end HypClass1
