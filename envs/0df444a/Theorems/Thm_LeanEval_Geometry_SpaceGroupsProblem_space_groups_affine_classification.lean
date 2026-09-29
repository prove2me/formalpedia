-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_space_groups_affine_classification
-- name    : LeanEval.Geometry.SpaceGroupsProblem.space_groups_affine_classification
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-06T05:55:57.032462+00:00
-- url     : https://prove2.me/theorems/4185c9df-935d-491d-8abb-cd750acaddc5
-- title:
--   A complete irredundant list of the $219$ affine classes of space groups
-- statement:
--   Work in $E=\mathbb R^3$ with its Euclidean metric, and let $\mathrm{Isom}(E)$ be the group of bijective affine isometries of $E$. Call a subgroup $G\le\mathrm{Isom}(E)$ *crystallographic* if (i) for every $x\in E$ and every $\varepsilon>0$ the set $\{g\in G:\operatorname{dist}(g(x),x)\le\varepsilon\}$ is finite, and (ii) there are three linearly independent vectors $v_1,v_2,v_3$ such that translation by each $v_i$ belongs to $G$.
--
--   For subgroups $G_1,G_2\le\mathrm{Isom}(E)$ write $G_1\sim G_2$ (*affinely equivalent*) if some invertible affine map $\varphi$ of $E$ satisfies $\varphi G_1\varphi^{-1}=G_2$ as sets of affine maps, and $G_1\sim_{+}G_2$ (*orientation-preserving affinely equivalent*) if such a $\varphi$ can be chosen with $\det(\varphi_{\mathrm{lin}})>0$.
--
--   This statement is the enumeration form of the count of $219$ affine classes: there is a list
--
--   $$
--   G_1,\dots,G_{219}
--   $$
--
--   of crystallographic groups in $\mathbb R^3$ that is
--
--   1. **complete**: every crystallographic group $G$ satisfies $G_i\sim G$ for some index $i$; and
--   2. **irredundant**: $G_i\sim G_j$ forces $i=j$.
--
--   Here the comparison map $\varphi$ is an arbitrary invertible affine map, with no constraint on the sign of its determinant, so an enantiomorphic pair of space groups becomes a single class. This is the convention under which the classical count drops from $230$ to $219$.
--
--   Combined with the fact that $\sim$ is an equivalence relation, the two conditions give the cardinality of the set of $\sim$-classes, and hence the count $219$.
--
--   **Formalization Note.** The list is given as a function $f$ from `Fin 219`; `CrystallographicGroup 3` and `AffinelyEquivalent` are the crystallographic-group subtype and the unrestricted affine conjugacy relation of the LeanEval definition bundle, used verbatim.
-- source:
--   LeanEval v1, problem space_groups_230; LeanEval/Geometry/SpaceGroups.lean, LeanEval.Geometry.SpaceGroupsProblem.space_groups, repository commit 296b7491ec989d21bcf8636a9a69231a1e5d1d25: https://github.com/leanprover/lean-eval/blob/296b7491ec989d21bcf8636a9a69231a1e5d1d25/LeanEval/Geometry/SpaceGroups.lean . Classification due to E. S. Fedorov (1891) and A. Schoenflies (1891), independently; background: Oliver Knill, Some Fundamental Theorems in Mathematics, section 94 (Crystallography), printed p. 41, https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf .

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem

theorem space_groups_affine_classification :
    ∃ f : Fin 219 → CrystallographicGroup 3,
      (∀ G : CrystallographicGroup 3, ∃ i : Fin 219, AffinelyEquivalent (f i).1 G.1) ∧
        (∀ i j : Fin 219, AffinelyEquivalent (f i).1 (f j).1 → i = j) := by
  sorry

end SpaceGroupsProblem
end Geometry
end LeanEval
