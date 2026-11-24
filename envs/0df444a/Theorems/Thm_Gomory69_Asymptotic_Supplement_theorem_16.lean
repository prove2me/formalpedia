-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_Supplement_theorem_16
-- name    : Gomory69.Asymptotic.Supplement.theorem_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:27:21.776182+00:00
-- url     : https://prove2.me/theorems/3b552949-5cbf-4750-b4b5-aaa9931e3648
-- title:
--   THEOREM 16 — Coordinate facets outside the order-two exception
-- statement:
--   Let $G$ be a finite Abelian group whose order is not $2$, let $g_0\in G$ and let $h\in G^+$. Then
--   $$t(h)\ge0\text{ is a facet of }P(G,g_0).$$
--   All finite Abelian groups outside the stated exception are included, with no prime-order or nonzero-target restriction.
--
--   This identifies the coordinate facets of the master polyhedra.
--
--   Differences from the source:
--   - reading: the page writes a coordinate h in G → h ranges over G minus zero; reason: T-space has no zero coordinate, by the p. 474 definition
--   - encoding: G is not cyclic of order 2 → the group cardinal is not 2; reason: every group of order 2 is cyclic; no other finite Abelian group is excluded
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), DOI 10.1016/0024-3795(69)90017-2, p. 480, THEOREM 16

import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron

namespace Gomory69.Asymptotic.Supplement

theorem theorem_16 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (h : Gomory69.Lifting.Plus G) (horder : Fintype.card G ≠ 2) :
    Gomory69.Lifting.IsFace G g₀ (fun g => if g = h then 1 else 0) 0 := by sorry

end Gomory69.Asymptotic.Supplement
