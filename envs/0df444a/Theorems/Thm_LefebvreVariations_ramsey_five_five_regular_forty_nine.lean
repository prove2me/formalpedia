-- Prove2me | Theorems.Thm_LefebvreVariations_ramsey_five_five_regular_forty_nine
-- name    : LefebvreVariations.ramsey_five_five_regular_forty_nine
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:59:31.233004+00:00
-- url     : https://prove2.me/theorems/6f78f282-b970-5d23-9b53-f97c2ab013eb
-- title:
--   Lefebvre's variations, No. 119 — on a theme by Ramsey: $R(5,5)\le 49$ for $24$-regular graphs on $49$ vertices
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $G$ be a simple graph on $49$ vertices that is $24$-regular, i.e. $\deg_G(v)=24$ for every vertex $v$. Then $G$ contains a clique on $5$ vertices (a $K_5$) or an independent set of $5$ vertices.
--
--   Equivalently: there is no $(5,5)$-graph on $49$ vertices that is $24$-regular. This is the content of the upper bound $R(5,5)\le 49$ of McKay and Radziszowski, restricted to the only degree that is possible a priori: in a $(5,5)$-graph $G$ on $49$ vertices, the neighbourhood of a vertex $v$ is a $(4,5)$-graph, so $\deg(v)\le R(4,5)-1=24$, and its non-neighbourhood is, in the complement, a $(4,5)$-graph as well, so $48-\deg(v)\le 24$; hence $\deg(v)=24$.
--
--   **Formalization Note** The graph is a `SimpleGraph (Fin 49)` with decidable adjacency; `G.degree v` is the number of neighbours of `v`. A $K_5$ is a `Finset` `s` with `G.IsNClique 5 s`, an independent $5$-set a `Finset` `s` with `Gᶜ.IsNClique 5 s` (a $5$-clique of the complement), as in the platform definition `Erdos77.asymmetricRamsey`. The degree condition is `hdeg : ∀ v, G.degree v = 24`.
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `RamseyValues.ramsey_five_five_le_49` ($R(5,5)\le 49$). The platform bound $R(4,5)=25$ (a milestone of the same mission) forces every vertex of a $(5,5)$-graph on $49$ vertices to have degree exactly $24$, because both its neighbourhood and its non-neighbourhood are $(4,5)$-graphs or complements of such, hence have at most $24$ vertices. This statement is exactly the remaining case, the $24$-regular graphs. It is a special case of the base statement (same conclusion, stronger hypothesis), and the base statement follows from it together with $R(4,5)\le 25$.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). B. D. McKay and S. P. Radziszowski, Subgraph counting identities and Ramsey numbers, J. Combin. Theory Ser. B 69 (1997), no. 2, 193–209 (proof of R(5,5) ≤ 49); the regularity comes from R(4,5) = 25 (B. D. McKay and S. P. Radziszowski, R(4,5) = 25, J. Graph Theory 19 (1995) 309–322). Angeltveit–McKay (J. Graph Theory 89 (2018) 5–13, arXiv:1703.08768) improved the bound to 48, which implies this statement (delete a vertex of a 24-regular graph on 49 vertices). Origin of this statement: it is the missing step of a reduction of RamseyValues.ramsey_five_five_le_49, a milestone of the mission RamseyValues.ramsey_five_five. Given R(4,5) ≤ 25 (platform milestone RamseyValues.ramsey_four_five), a (5,5)-graph on 49 vertices must be 24-regular, so R(5,5) ≤ 49 follows from this regular case.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

theorem ramsey_five_five_regular_forty_nine (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v = 24) :
    (∃ s : Finset (Fin 49), G.IsNClique 5 s) ∨ (∃ s : Finset (Fin 49), Gᶜ.IsNClique 5 s) := by
  sorry

end LefebvreVariations
