-- Prove2me | Theorems.Thm_HadwigerConj_colorable_of_isDegenerate
-- name    : HadwigerConj.colorable_of_isDegenerate
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T23:39:58.380783+00:00
-- url     : https://prove2.me/theorems/79bcada1-5404-4307-955a-25c517497917
-- title:
--   Theorem 3.1: $k$-degenerate graphs are $(k+1)$-colourable
-- statement:
--   Let $G$ be a finite graph and $k\ge 0$. If $G$ is $k$-degenerate (every nonempty set $S$ of vertices contains a vertex with at most $k$ neighbours in $S$), then
--
--   $$\chi(G)\le k+1.$$
--
--   This converts bounds on degeneracy (for instance from average-degree bounds for graphs excluding a minor) into colouring bounds.
-- source:
--   P. Seymour, "Hadwiger's conjecture" (survey), in: Open Problems in Mathematics, Springer, 2016 (uploaded PDF `paper.pdf`), Theorem 3.1 (p. 4)

import Mathlib
import Definitions.Def_HadwigerConj_Defs

namespace HadwigerConj
theorem colorable_of_isDegenerate {V : Type} [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hG : IsDegenerate G k) : G.Colorable (k + 1) := by sorry
end HadwigerConj
