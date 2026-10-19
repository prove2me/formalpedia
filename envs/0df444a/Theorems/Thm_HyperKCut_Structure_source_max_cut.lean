-- Prove2me | Theorems.Thm_HyperKCut_Structure_source_max_cut
-- name    : HyperKCut.Structure.source_max_cut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:05.636052+00:00
-- url     : https://prove2.me/theorems/c1076b75-e26f-4017-91ab-1d234ea2e6ba
-- title:
--   §1.1, p. 3 — uniqueness of the source-maximal and source-minimal minimum terminal cuts
-- statement:
--   Let $S,T\subseteq V$ be disjoint sets in a finite unit-cost hypergraph. There is exactly one minimum $(S,T)$-terminal cut whose source set contains the source set of every other minimum $(S,T)$-terminal cut (the source-maximal one), and exactly one whose source set is contained in the source set of every minimum $(S,T)$-terminal cut (the source-minimal one):
--
--   $$\exists!\,U\subseteq V:\ U\text{ is source-maximal among minimum }(S,T)\text{-terminal cuts}, \qquad \exists!\,U\subseteq V:\ U\text{ is source-minimal among minimum }(S,T)\text{-terminal cuts}.$$
--
--   This identifies the canonical terminal cut used in Theorem 1.2 and Claim 4.2.
--
--   **Formalization Note** The paper also states polynomial-time computability; this milestone isolates its existence and uniqueness claim and does not state a running-time result.
-- source:
--   Chandrasekaran & Chekuri, Hypergraph k-cut for fixed k in deterministic polynomial time, arXiv:2009.12442v1, p. 3 (PDF 4), §1.1, paragraph beginning “Let S, T be disjoint subsets”

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

namespace HyperKCut.Structure

variable {V : Type} [Fintype V] [DecidableEq V]

/-- §1.1, p. 3: the source-maximal and the source-minimal minimum terminal cuts
exist and are unique. -/
theorem source_max_cut (H : Hypergraph V) (S T : Finset V)
    (hST : Disjoint S T) :
    (∃! U : Finset V, IsSourceMaxMinTerminalCut H S T U) ∧
    (∃! U : Finset V, IsMinTerminalCut H S T U ∧
      ∀ U' : Finset V, IsMinTerminalCut H S T U' → U ⊆ U') := by sorry

end HyperKCut.Structure
