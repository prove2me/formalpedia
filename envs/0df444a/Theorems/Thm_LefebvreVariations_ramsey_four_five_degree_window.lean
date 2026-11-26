-- Prove2me | Theorems.Thm_LefebvreVariations_ramsey_four_five_degree_window
-- name    : LefebvreVariations.ramsey_four_five_degree_window
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:02:56.000735+00:00
-- url     : https://prove2.me/theorems/46cff6dc-dc09-42b8-bc25-1bc69ad06bd8
-- title:
--   Lefebvre's variations, No. 7 — on a theme by Ramsey: $R(4,5)\le 25$ for graphs with all degrees in $[7,13]$
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $G$ be a simple graph on $25$ vertices in which every vertex $v$ has degree
--   $$
--   7 \le \deg_G(v) \le 13 .
--   $$
--   Then $G$ contains a clique on $4$ vertices (a $K_4$) or an independent set of $5$ vertices.
--
--   Equivalently: there is no $(4,5)$-graph on $25$ vertices (a graph with no $K_4$ and no independent $5$-set) all of whose degrees lie in $[7,13]$. This is the content of the upper bound $R(4,5)\le 25$ of McKay and Radziszowski, restricted to the only degrees that are possible a priori: in a $(4,5)$-graph on $25$ vertices, the neighbourhood of a vertex $v$ is a $(3,5)$-graph, so $\deg(v)\le R(3,5)-1=13$, and its non-neighbourhood is a $(4,4)$-graph, so $24-\deg(v)\le R(4,4)-1=17$, i.e. $\deg(v)\ge 7$. Together with the explicit circulant $(4,5)$-graph on $\mathbb{Z}/24$ with connection set $\{\pm1,\pm2,\pm4,\pm8,\pm9\}$, it gives $R(4,5)=25$.
--
--   **Formalization Note** The graph is a `SimpleGraph (Fin 25)` with decidable adjacency, and `G.degree v` is the number of neighbours of `v`. A $K_4$ is a `Finset` `s` with `G.IsNClique 4 s`; an independent $5$-set is a `Finset` `s` with `Gᶜ.IsNClique 5 s` (a $5$-clique of the complement graph), exactly as in the platform definition `Erdos77.asymmetricRamsey`. The degree window is the hypothesis `hdeg : ∀ v, 7 ≤ G.degree v ∧ G.degree v ≤ 13`.
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `RamseyValues.ramsey_four_five` ($R(4,5)=25$). The lower bound is the explicit circulant graph on $24$ vertices, and the upper bound $R(4,5) \le 25$ is the computer-assisted theorem of McKay and Radziszowski. In a graph on $25$ vertices with no $K_4$ and no independent $5$-set, the proved bounds $R(3,5) \le 14$ and $R(4,4) \le 18$ force every degree into $[7,13]$. This statement is the upper bound restricted to those degrees. It is a special case of the base upper bound, and the base statement follows from it together with the proved parts.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). B. D. McKay and S. P. Radziszowski, R(4,5) = 25, J. Graph Theory 19 (1995), no. 3, 309–322 (computer-assisted proof that no graph on 25 vertices is K4-free with independence number at most 4; the statement here is that theorem restricted to graphs with all degrees in [7,13]). The lower bound R(4,5) ≥ 25 is due to J. G. Kalbfleisch, Construction of special edge-chromatic graphs, Canad. Math. Bull. 8 (1965) 575–584; the degree window comes from R(3,5) = 14 and R(4,4) = 18 (R. E. Greenwood and A. M. Gleason, Combinatorial relations and chromatic graphs, Canad. J. Math. 7 (1955) 1–7). Origin of this statement: it is the missing step of a reduction of RamseyValues.ramsey_four_five (R(4,5) = 25), a milestone of the mission RamseyValues.ramsey_five_five. That reduction proves R(3,5) ≤ 14 and R(4,4) ≤ 18 (Erdős–Szekeres recursion plus the Greenwood–Gleason parity step), deduces that every (4,5)-graph on 25 vertices has all degrees in [7,13], and proves R(4,5) ≥ 25 by checking the circulant graph on Z/24 with connection set {±1, ±2, ±4, ±8, ±9} by kernel evaluation.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

theorem ramsey_four_five_degree_window (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj]
    (hdeg : ∀ v, 7 ≤ G.degree v ∧ G.degree v ≤ 13) :
    (∃ s : Finset (Fin 25), G.IsNClique 4 s) ∨ (∃ s : Finset (Fin 25), Gᶜ.IsNClique 5 s) := by
  sorry

end LefebvreVariations
