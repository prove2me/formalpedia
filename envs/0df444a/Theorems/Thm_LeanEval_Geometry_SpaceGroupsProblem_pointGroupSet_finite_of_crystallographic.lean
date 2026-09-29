-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_pointGroupSet_finite_of_crystallographic
-- name    : LeanEval.Geometry.SpaceGroupsProblem.pointGroupSet_finite_of_crystallographic
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T07:24:57.460717+00:00
-- url     : https://prove2.me/theorems/352cd28a-b0da-4616-879c-ee42b3189d7a
-- title:
--   The point group of a crystallographic group is finite
-- statement:
--   Let $G$ be a **crystallographic group** in dimension $d$: a subgroup of the Euclidean motion group $E_d$ of $\mathbb{R}^d$ that is discrete (for every point $x$ and every $\varepsilon>0$ only finitely many $g\in G$ move $x$ by at most $\varepsilon$) and contains $d$ linearly independent translations. Its **point group** is the set of linear parts of its elements,
--
--   $$P(G)=\{\mathrm{lin}(g)\;:\;g\in G\}\subseteq O(d).$$
--
--   The theorem asserts that $P(G)$ is a **finite** set.
--
--   This is the first structural finiteness statement in the theory of space groups: a crystallographic group has only finitely many possible rotational/reflective parts, so it is an extension of a finite group by its lattice of translations. It is the step that makes a classification of crystallographic groups into finitely many types conceivable.
-- source:
--   L. S. Charlap, Bieberbach Groups and Flat Manifolds, Springer 1986, Chapter I, Theorem 1.2 (the point group of a crystallographic group is finite).

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupsPointGroupDefs

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem

theorem pointGroupSet_finite_of_crystallographic {d : ℕ} {G : Subgroup (EuclideanIsom d)}
    (hG : IsCrystallographicGroup G) : (pointGroupSet G).Finite := by sorry

end SpaceGroupsProblem
end Geometry
end LeanEval
