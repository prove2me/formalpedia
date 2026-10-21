-- Prove2me | Theorems.Thm_HyperKCut_Structure_theorem_1_2
-- name    : HyperKCut.Structure.theorem_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:37.801097+00:00
-- url     : https://prove2.me/theorems/c9e6d197-c5d3-4943-bf03-967e8328fec8
-- title:
--   Theorem 1.2 — first part recovered as a source-maximal minimum terminal cut
-- statement:
--   Let $G=(V,E)$ be a finite hypergraph, let $k\ge2$, and let $(V_1,\ldots,V_k)$ be a maximal minimum $k$-partition with $|V_1|\ge2k-2$. For every $T\subseteq V\setminus V_1$ meeting each $V_j$ for $j=2,\ldots,k$, there exists a set $S$ such that
--
--   $$S\subseteq V_1,\qquad |S|=2k-2,\qquad V_1\text{ is the source-maximal minimum }(S,T)\text{-terminal source set}.$$
--
--   This is the paper's principal structural result for recovering a part of an optimum hypergraph k-partition.
--
--   **Formalization Note** The partition is ordered; its first part is `P 0`. The source-maximal predicate means minimum value and containment of every other minimum terminal source set. The cardinality of $S$ is exact.
-- source:
--   Chandrasekaran & Chekuri, Hypergraph k-cut for fixed k in deterministic polynomial time, arXiv:2009.12442v1, p. 4 (PDF 5), Theorem 1.2 (restated p. 17, PDF 18)

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

namespace HyperKCut.Structure

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Theorem 1.2, p. 4: the first part is a source-maximal minimum terminal cut. -/
theorem theorem_1_2 (H : Hypergraph V) (k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (P : Fin k → Finset V) (hP : IsMaximalMinKPartition H k P)
    (hV1 : 2 * k - 2 ≤ (P 0).card)
    (T : Finset V) (hT : T ⊆ (P 0)ᶜ)
    (hTj : ∀ j : Fin k, j ≠ 0 → (T ∩ P j).Nonempty) :
    ∃ S : Finset V, S ⊆ P 0 ∧ S.card = 2 * k - 2 ∧
      IsSourceMaxMinTerminalCut H S T (P 0) := by sorry

end HyperKCut.Structure
