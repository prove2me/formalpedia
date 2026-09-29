-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_pointGroup_integral_matrix
-- name    : LeanEval.Geometry.SpaceGroupsProblem.pointGroup_integral_matrix
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T07:36:55.237487+00:00
-- url     : https://prove2.me/theorems/5518e716-403b-482d-b54d-114bc0abc241
-- title:
--   The point group of a crystallographic group is integral in a lattice basis
-- statement:
--   Let $G$ be a **crystallographic group** in dimension $d$ — a discrete subgroup of the Euclidean motion group $E_d$ containing $d$ linearly independent translations — with translation lattice $T(G)$ and point group $P(G)$, the group of linear parts of the elements of $G$.
--
--   The theorem asserts that one may choose a basis adapted to the lattice in which every element of the point group becomes an **integer matrix**: there are vectors $w_1,\dots,w_d$, linearly independent over $\mathbb{R}$, with $T(G)=\mathbb{Z}w_1\oplus\cdots\oplus\mathbb{Z}w_d$, such that for every $A\in P(G)$ there is a matrix $M\in M_d(\mathbb{Z})$ with
--
--   $$A w_j=\sum_{i=1}^{d} M_{ij}\,w_i \qquad (1\le j\le d).$$
--
--   Equivalently, the point group acts on the translation lattice $T(G)\cong\mathbb{Z}^d$ by $\mathbb{Z}$-linear automorphisms, so that $P(G)$ is represented inside $GL_d(\mathbb{Z})$. This integrality is the source of the arithmetic constraints on point groups, such as the crystallographic restriction on the possible orders of their elements.
-- source:
--   L. S. Charlap, Bieberbach Groups and Flat Manifolds, Springer 1986, Chapter I, Section 2 (the holonomy/point group acts on the translation lattice, giving an integral representation).

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupsPointGroupDefs

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem

theorem pointGroup_integral_matrix {d : ℕ} {G : Subgroup (EuclideanIsom d)}
    (hG : IsCrystallographicGroup G) :
    ∃ w : Fin d → E d, LinearIndependent ℝ w ∧
      Submodule.span ℤ (Set.range w) = transSubmoduleZ G ∧
      ∀ A ∈ pointGroup G, ∃ M : Matrix (Fin d) (Fin d) ℤ,
        ∀ j, A (w j) = ∑ i, (M i j : ℝ) • w i := by sorry

end SpaceGroupsProblem
end Geometry
end LeanEval
