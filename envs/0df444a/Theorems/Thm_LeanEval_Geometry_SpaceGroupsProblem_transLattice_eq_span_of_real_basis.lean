-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_transLattice_eq_span_of_real_basis
-- name    : LeanEval.Geometry.SpaceGroupsProblem.transLattice_eq_span_of_real_basis
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T07:25:11.09772+00:00
-- url     : https://prove2.me/theorems/4b543946-93bf-4aa3-913d-1936e598c330
-- title:
--   The translation subgroup of a crystallographic group is a full-rank lattice
-- statement:
--   Let $G$ be a **crystallographic group** in dimension $d$: a discrete subgroup of the Euclidean motion group $E_d$ of $\mathbb{R}^d$ containing $d$ linearly independent translations. Write $T(G)\subseteq\mathbb{R}^d$ for its set of translation vectors, an additive subgroup of $\mathbb{R}^d$ (the *translation lattice*).
--
--   The theorem asserts that $T(G)$ is a **full-rank lattice**: there are vectors $w_1,\dots,w_d\in\mathbb{R}^d$ that are linearly independent over $\mathbb{R}$ and satisfy
--
--   $$T(G)=\mathbb{Z}w_1\oplus\cdots\oplus\mathbb{Z}w_d.$$
--
--   In other words the translations of $G$ form a discrete cocompact subgroup of $\mathbb{R}^d$ with a basis consisting of $d$ independent vectors. This identification of the translation subgroup with a lattice $\mathbb{Z}^d$ is what allows the point group to be represented by integer matrices.
-- source:
--   L. S. Charlap, Bieberbach Groups and Flat Manifolds, Springer 1986, Chapter I, Section 1 (translation subgroup of a crystallographic group is a lattice of rank d).

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupsPointGroupDefs

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem

theorem transLattice_eq_span_of_real_basis {d : ℕ} {G : Subgroup (EuclideanIsom d)}
    (hG : IsCrystallographicGroup G) :
    ∃ w : Fin d → E d, LinearIndependent ℝ w ∧
      Submodule.span ℤ (Set.range w) = transSubmoduleZ G := by sorry

end SpaceGroupsProblem
end Geometry
end LeanEval
