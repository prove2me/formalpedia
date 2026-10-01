-- Prove2me | Theorems.Thm_HadwigerConj_exists_degree_le_two_of_no_K4_minor
-- name    : HadwigerConj.exists_degree_le_two_of_no_K4_minor
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T23:13:33.771143+00:00
-- url     : https://prove2.me/theorems/e466add6-0967-4f4b-b60b-7c48d5dbac28
-- title:
--   Graphs with no $K_4$ minor have a vertex of degree at most $2$
-- statement:
--   Let $G$ be a finite graph with at least one vertex. If $G$ has no $K_4$ minor, then $G$ has a vertex of degree at most two:
--
--   $$K_4\not\preceq G,\ V(G)\neq\emptyset\ \Longrightarrow\ \exists v\in V(G):\ \deg_G(v)\le 2.$$
--
--   Applied to every subgraph, this says graphs with no $K_4$ minor are $2$-degenerate, which gives $\mathrm{HC}(3)$ via greedy colouring.
-- source:
--   P. Seymour, "Hadwiger's conjecture" (survey), in: Open Problems in Mathematics, Springer, 2016 (uploaded PDF `paper.pdf`), Section 2 (p. 2: “Hadwiger showed that every non-null graph with no K4 minor has a vertex of degree at most two”); Wikipedia, "Hadwiger conjecture (graph theory)", https://en.wikipedia.org/wiki/Hadwiger_conjecture_(graph_theory), section “Special cases and partial results”

import Mathlib
import Definitions.Def_HadwigerConj_Defs

namespace HadwigerConj
theorem exists_degree_le_two_of_no_K4_minor {V : Type} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (hG : ¬ HasCompleteMinor G 4) :
    ∃ v : V, (G.neighborSet v).ncard ≤ 2 := by sorry
end HadwigerConj
