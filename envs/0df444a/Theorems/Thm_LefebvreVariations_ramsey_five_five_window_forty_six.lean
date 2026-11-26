-- Prove2me | Theorems.Thm_LefebvreVariations_ramsey_five_five_window_forty_six
-- name    : LefebvreVariations.ramsey_five_five_window_forty_six
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:02:57.231993+00:00
-- url     : https://prove2.me/theorems/9ef1362f-1a30-5d6a-b082-4c6732380864
-- title:
--   Lefebvre's variations, No. 133 — on a theme by Ramsey: $R(5,5)\le 46$ for graphs on $46$ vertices with all degrees in $[21,24]$
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $G$ be a simple graph on $46$ vertices in which every vertex $v$ has degree
--   $$
--   21 \le \deg_G(v) \le 24 .
--   $$
--   Then $G$ contains a clique on $5$ vertices (a $K_5$) or an independent set of $5$ vertices.
--
--   Equivalently: there is no $(5,5)$-graph on $46$ vertices with all degrees in $[21,24]$. This is the content of the theorem $R(5,5)\le 46$ of Angeltveit and McKay restricted to the only degrees that are possible a priori: in a $(5,5)$-graph on $46$ vertices the neighbourhood of a vertex $v$ is a $(4,5)$-graph, so $\deg(v)\le R(4,5)-1=24$, and the non-neighbourhood is, in the complement, a $(4,5)$-graph too, so $45-\deg(v)\le 24$, i.e. $\deg(v)\ge 21$.
--
--   **Formalization Note** The graph is a `SimpleGraph (Fin 46)` with decidable adjacency; `G.degree v` is the number of neighbours of `v`. A $K_5$ is a `Finset` `s` with `G.IsNClique 5 s`, an independent $5$-set a `Finset` `s` with `Gᶜ.IsNClique 5 s`, as in `Erdos77.asymmetricRamsey`. The degree window is `hdeg : ∀ v, 21 ≤ G.degree v ∧ G.degree v ≤ 24`.
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `RamseyValues.ramsey_five_five_le_46` ($R(5,5)\le 46$, the current record). The bound $R(4,5)=25$ forces every degree of a $(5,5)$-graph on $46$ vertices into $[21,24]$ (neighbourhood and non-neighbourhood are $(4,5)$-graphs or complements of such, hence have at most $24$ vertices). This statement is the base statement restricted to those degrees: it is a special case of the base statement, and the base statement follows from it together with $R(4,5)\le 25$.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). V. Angeltveit and B. D. McKay, R(5,5) ≤ 46, arXiv:2409.15709 (the statement here is the main theorem restricted to graphs with all degrees in [21,24], the only degrees a (5,5)-graph on 46 vertices can have by R(4,5) = 25, McKay–Radziszowski, J. Graph Theory 19 (1995) 309–322). Origin of this statement: it is the missing step of a reduction of RamseyValues.ramsey_five_five_le_46, a milestone of the mission RamseyValues.ramsey_five_five. Given R(4,5) ≤ 25 (platform milestone RamseyValues.ramsey_four_five), every (5,5)-graph on 46 vertices has all degrees in [21,24], so R(5,5) ≤ 46 follows from this window statement.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

theorem ramsey_five_five_window_forty_six (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj]
    (hdeg : ∀ v, 21 ≤ G.degree v ∧ G.degree v ≤ 24) :
    (∃ s : Finset (Fin 46), G.IsNClique 5 s) ∨ (∃ s : Finset (Fin 46), Gᶜ.IsNClique 5 s) := by
  sorry

end LefebvreVariations
