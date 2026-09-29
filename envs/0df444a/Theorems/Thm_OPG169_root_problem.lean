-- Prove2me | Theorems.Thm_OPG169_root_problem
-- name    : OPG169.root_problem
-- status  : Open
-- author  : @hao jia
-- created : 2026-09-08T05:06:07.474867+00:00
-- url     : https://prove2.me/theorems/9b1ff3fb-ebe6-43b3-8176-9e1e593b5204
-- title:
--   OPG-169: the Two Color Conjecture for planar digraphs
-- statement:
--   For every orientation $D$ of a finite simple planar graph, there exists a vertex coloring $c:V(D)\to\{0,1\}$ such that both full induced color classes are acyclic:
--
--   $$
--   D[c^{-1}(0)]\text{ is acyclic}
--   \qquad\text{and}\qquad
--   D[c^{-1}(1)]\text{ is acyclic}.
--   $$
--
--   The color classes need not be independent, and either class may be empty. Directed triangles are allowed in the input.
-- source:
--   Open Problem Garden / UnsolvedMath OPG-169, https://www.unsolvedmath.com/problems/OPG-169

import Definitions.Def_opg169_planar_dichromatic

namespace OPG169

universe u

/-- OPG-169: every orientation of a finite simple planar graph admits a
vertex two-coloring whose two induced color classes are acyclic. -/
theorem root_problem
    {V : Type u} [Fintype V] (G : SimpleGraph V) (D : Digraph V)
    (hplanar : IsPlanar G) (horientation : IsOrientationOf D G) :
    HasAcyclicTwoColoring D := by sorry

end OPG169
