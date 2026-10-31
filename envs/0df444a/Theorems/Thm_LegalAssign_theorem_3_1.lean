-- Prove2me | Theorems.Thm_LegalAssign_theorem_3_1
-- name    : LegalAssign.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:23:34.100335+00:00
-- url     : https://prove2.me/theorems/4eba55ae-314e-4943-b622-c4fe98369923
-- title:
--   Theorem 3.1 — the unique legal set is the set of stable assignments of the subinstance $G_L$
-- statement:
--   Let $(G,<,q)$ be an instance of the stable assignment problem. There is a unique set $\mathcal L\subseteq\mathcal M(G,q)$ with the legal property. This set coincides with the set of stable assignments of $(G_L,<,q)$, where $G_L$ is a subgraph of $G$. Moreover,
--   $$E(G_L)=\bigcup\{M:M\in\mathcal S(G_L,<,q)\}=\bigcup\{M:M\in\mathcal L\}.$$
--
--   The theorem says that legal assignments are stable assignments in disguise, so the structural and algorithmic theory of stable assignments applies to them.
--
--   **Formalization Note** Uniqueness is among all subsets of $\mathcal M(G,q)$ with the legal property. The first conjunct of the Lean statement is existence and uniqueness; the second states the remaining clauses for any set with the legal property.
--
--   Differences from the source:
--   - encoding: <_v is a strict ordering of the neighbours of v in G → prefA a and prefB b are strict total orders on the whole other side; reason: only comparisons among neighbours ever enter, and every strict order on the neighbours extends to the whole side
--   - encoding: G is a bipartite graph, finite throughout the paper → Fintype A, Fintype B, E : Finset (A × B), assignments are Finsets of pairs; reason: Lean convention; the same instances
--   - reading: q = {q_b} ∈ ℕ^B, with no statement on whether this ℕ contains 0 → q : B → ℕ, so q_b = 0 is allowed; reason: the source does not settle it, and the Lean statement covers positive quotas and quota 0 alike
--   - reading: G_L is a subgraph of G → G_L := G[⋃{M : M ∈ 𝓛}], with ⋃{M : M ∈ 𝓛} ⊆ E stated as a clause; reason: the last display forces this edge set and §3, p.8 defines G_L this way; the statement implies the printed existential
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, Theorem 3.1, p.7; definition of G_L, §3, p.8

import Mathlib
import Definitions.Def_LegalAssign_Instance

namespace LegalAssign

/-- Theorem 3.1 (arXiv:1809.08506v2, p.7). There is a unique `𝓛 ⊆ 𝓜(G, q)` with the legal property. It
is the set of stable assignments of `(G_L, <, q)`, where `G_L := G[⋃{M : M ∈ 𝓛}]` is a subgraph of
`G`, and `E(G_L) = ⋃{M : M ∈ 𝓢(G_L, <, q)} = ⋃{M : M ∈ 𝓛}`.

**Formalization Note** The source says only that `G_L` is a subgraph of `G`. Its last display forces
the edge set, and §3 (p.8) defines `G_L := G[⋃{M : M ∈ 𝓛}]`, which is the graph taken here. -/
theorem theorem_3_1 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) :
    (∃! L : Set (Finset (A × B)), L ⊆ G.assignments ∧ G.HasLegalProperty L) ∧
    ∀ L : Set (Finset (A × B)), L ⊆ G.assignments → G.HasLegalProperty L →
      edgeUnion L ⊆ G.E ∧
      L = (G.restrict (edgeUnion L)).stable ∧
      (G.restrict (edgeUnion L)).E = edgeUnion (G.restrict (edgeUnion L)).stable ∧
      (G.restrict (edgeUnion L)).E = edgeUnion L := by sorry

end LegalAssign
