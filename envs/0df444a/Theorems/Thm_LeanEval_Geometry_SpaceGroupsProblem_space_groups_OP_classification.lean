-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_space_groups_OP_classification
-- name    : LeanEval.Geometry.SpaceGroupsProblem.space_groups_OP_classification
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-06T05:55:55.846946+00:00
-- url     : https://prove2.me/theorems/b706a289-4328-4042-a7b9-ea6146c69195
-- title:
--   A complete irredundant list of the $230$ space-group types
-- statement:
--   Work in $E=\mathbb R^3$ with its Euclidean metric, and let $\mathrm{Isom}(E)$ be the group of bijective affine isometries of $E$. Call a subgroup $G\le\mathrm{Isom}(E)$ *crystallographic* if (i) for every $x\in E$ and every $\varepsilon>0$ the set $\{g\in G:\operatorname{dist}(g(x),x)\le\varepsilon\}$ is finite, and (ii) there are three linearly independent vectors $v_1,v_2,v_3$ such that translation by each $v_i$ belongs to $G$.
--
--   For subgroups $G_1,G_2\le\mathrm{Isom}(E)$ write $G_1\sim G_2$ (*affinely equivalent*) if some invertible affine map $\varphi$ of $E$ satisfies $\varphi G_1\varphi^{-1}=G_2$ as sets of affine maps, and $G_1\sim_{+}G_2$ (*orientation-preserving affinely equivalent*) if such a $\varphi$ can be chosen with $\det(\varphi_{\mathrm{lin}})>0$.
--
--   This statement is the enumeration form of the classical count of $230$ space-group types: there is a list
--
--   $$
--   G_1,\dots,G_{230}
--   $$
--
--   of crystallographic groups in $\mathbb R^3$ that is
--
--   1. **complete**: every crystallographic group $G$ satisfies $G_i\sim_{+}G$ for some index $i$; and
--   2. **irredundant**: $G_i\sim_{+}G_j$ forces $i=j$.
--
--   Equivalently, the crystallographic groups of $\mathbb R^3$ fall into exactly $230$ classes under orientation-preserving affine conjugacy, the classification of Fedorov and Schoenflies. Completeness is the substantive half — it asserts that no crystallographic group escapes the list — while irredundancy says the $230$ listed groups are pairwise inequivalent, so that enantiomorphic (chiral) partners are counted separately.
--
--   Combined with the fact that $\sim_{+}$ is an equivalence relation, the two conditions give the cardinality of the set of $\sim_{+}$-classes, and hence the count $230$.
--
--   **Formalization Note.** The list is given as a function $f$ from `Fin 230`; `CrystallographicGroup 3` is the subtype of subgroups of the affine isometry group of `EuclideanSpace ℝ (Fin 3)` satisfying the two conditions above, and `AffOPEquivalent` is the orientation-preserving affine conjugacy relation, both taken verbatim from the LeanEval definition bundle.
-- source:
--   LeanEval v1, problem space_groups_230; LeanEval/Geometry/SpaceGroups.lean, LeanEval.Geometry.SpaceGroupsProblem.space_groups, repository commit 296b7491ec989d21bcf8636a9a69231a1e5d1d25: https://github.com/leanprover/lean-eval/blob/296b7491ec989d21bcf8636a9a69231a1e5d1d25/LeanEval/Geometry/SpaceGroups.lean . Classification due to E. S. Fedorov (1891) and A. Schoenflies (1891), independently; background: Oliver Knill, Some Fundamental Theorems in Mathematics, section 94 (Crystallography), printed p. 41, https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf .

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem

theorem space_groups_OP_classification :
    ∃ f : Fin 230 → CrystallographicGroup 3,
      (∀ G : CrystallographicGroup 3, ∃ i : Fin 230, AffOPEquivalent (f i).1 G.1) ∧
        (∀ i j : Fin 230, AffOPEquivalent (f i).1 (f j).1 → i = j) := by
  sorry

end SpaceGroupsProblem
end Geometry
end LeanEval
