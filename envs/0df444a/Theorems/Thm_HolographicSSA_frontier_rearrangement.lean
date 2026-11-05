-- Prove2me | Theorems.Thm_HolographicSSA_frontier_rearrangement
-- name    : HolographicSSA.frontier_rearrangement
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:58.556213+00:00
-- url     : https://prove2.me/theorems/d4bf3141-90ad-497f-9018-300e453046ef
-- title:
--   The surfaces of $r\cup s$ and $r\cap s$ are a rearrangement of those of $r$ and $s$
-- statement:
--   Let $X$ be a topological space and $r,s\subseteq X$, and write $\partial$ for the topological frontier. Then
--
--   1. $\partial(r\cup s)\cup\partial(r\cap s)\subseteq\partial r\cup\partial s$, and
--   2. $\partial(r\cup s)\cap\partial(r\cap s)\subseteq\partial r\cap\partial s$.
--
--   With $r=r_A$, $s=r_B$ the bulk regions of the boundary regions $A$, $B$, the frontiers $\partial(r_A\cup r_B)$ and $\partial(r_A\cap r_B)$ are the surfaces $m_{A\cup B}$ and $m_{A\cap B}$ of the paper, so clause 1 is footnote 3's inclusion $m_{A\cup B}\cup m_{A\cap B}\subset m_A\cup m_B$, and clause 2 says that no piece of $m_A\cup m_B$ is used twice unless it already lies in both. Together they are the set-level content of "simply rearrangements of $m_A$ and $m_B$" and give the area inequality of footnote 3.
--
--   **Formalization Note** The surface of a region is its topological frontier in the bulk, as in the definition of the holographic entropy.
--
--   Differences from the source:
--   - generalization: the bulk surfaces $m_{A\cup B}$, $m_{A\cap B}$, $m_A$, $m_B$ of the regions $r_A\cup r_B$, $r_A\cap r_B$, $r_A$, $r_B$ in the bulk slice → the frontiers of $r\cup s$, $r\cap s$, $r$, $s$ for arbitrary subsets $r,s$ of an arbitrary topological space; reason: the regions of the paper are subsets of the bulk slice, a topological space, so the paper's inclusion is the instance $r=r_A$, $s=r_B$
--   - generalization: the inclusion $m_{A\cup B}\cup m_{A\cap B}\subset m_A\cup m_B$ → that inclusion and also $\partial(r\cup s)\cap\partial(r\cap s)\subseteq\partial r\cap\partial s$; reason: the second clause is the multiplicity part of "simply rearrangements of $m_A$ and $m_B$" (p.6) on which footnote 3's area inequality rests; the conclusion contains the printed inclusion as its first clause
-- source:
--   Headrick, Takayanagi, A holographic proof of the strong subadditivity of entanglement entropy, arXiv:0704.3719v1, footnote 3, p.6 (PDF p.7)

import Mathlib

namespace HolographicSSA

/-- **The rearranged surfaces lie inside the old ones** (Headrick, Takayanagi, arXiv:0704.3719v1,
footnote 3, p.6): "In this sentence we've assumed the generic situation that mA and mB intersect
along (spatially) codimension 2 submanifolds. More generally we have mA∪B ∪ mA∩B ⊂ mA ∪ mB".

For any two subsets `r, s` of a topological space `X`,
1. `frontier (r ∪ s) ∪ frontier (r ∩ s) ⊆ frontier r ∪ frontier s`, and
2. `frontier (r ∪ s) ∩ frontier (r ∩ s) ⊆ frontier r ∩ frontier s`.

**Formalization Note** The surface of a bulk region is its topological frontier (see
`HolographicSSA.holographicEntropy`). Clause 2 is not printed: it is the multiplicity part of
"simply rearrangements of mA and mB" (p.6), and the area inequality of footnote 3 rests on it. -/
theorem frontier_rearrangement {X : Type*} [TopologicalSpace X] (r s : Set X) :
    frontier (r ∪ s) ∪ frontier (r ∩ s) ⊆ frontier r ∪ frontier s ∧
      frontier (r ∪ s) ∩ frontier (r ∩ s) ⊆ frontier r ∩ frontier s := by sorry

end HolographicSSA
