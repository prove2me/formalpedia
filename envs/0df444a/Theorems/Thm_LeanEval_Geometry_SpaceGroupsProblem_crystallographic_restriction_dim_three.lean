-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_crystallographic_restriction_dim_three
-- name    : LeanEval.Geometry.SpaceGroupsProblem.crystallographic_restriction_dim_three
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T07:42:21.946409+00:00
-- url     : https://prove2.me/theorems/0f4ab740-fa44-4edd-abca-38ed366bc314
-- title:
--   Crystallographic restriction theorem in dimension three
-- statement:
--   **Crystallographic restriction theorem in dimension three.** Let $G$ be a crystallographic group in $\mathbb{R}^3$: a discrete subgroup of the Euclidean motion group $E_3$ containing three linearly independent translations. Let $P(G)$ be its point group, the group of linear parts of the elements of $G$.
--
--   Then every $A\in P(G)$ has finite order, and
--
--   $$\operatorname{ord}(A)\in\{1,2,3,4,6\}.$$
--
--   Equivalently, a crystal in three-dimensional space can only have $1$-, $2$-, $3$-, $4$- and $6$-fold symmetry axes; five-fold and $n$-fold symmetry for $n\ge 7$ are impossible. The restriction comes from the interaction of two constraints on $A$: it preserves the translation lattice of $G$, so its trace is an integer, and it is an isometry, so its eigenvalues have modulus $1$. This is the classical arithmetic obstruction underlying the finiteness of the list of crystal classes and, ultimately, of the $230$ space groups.
-- source:
--   Classical; see e.g. M. Senechal, Crystalline Symmetries: An Informal Mathematical Introduction, Adam Hilger 1990, Chapter 2 (crystallographic restriction), or L. S. Charlap, Bieberbach Groups and Flat Manifolds, Springer 1986, Chapter I.

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupsPointGroupDefs

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem

theorem crystallographic_restriction_dim_three {G : Subgroup (EuclideanIsom 3)}
    (hG : IsCrystallographicGroup G) {A : E 3 ≃ₗᵢ[ℝ] E 3} (hA : A ∈ pointGroup G) :
    orderOf A = 1 ∨ orderOf A = 2 ∨ orderOf A = 3 ∨ orderOf A = 4 ∨ orderOf A = 6 := by sorry

end SpaceGroupsProblem
end Geometry
end LeanEval
