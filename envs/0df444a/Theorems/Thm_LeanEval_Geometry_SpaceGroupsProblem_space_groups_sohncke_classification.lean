-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_space_groups_sohncke_classification
-- name    : LeanEval.Geometry.SpaceGroupsProblem.space_groups_sohncke_classification
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-06T05:56:06.177212+00:00
-- url     : https://prove2.me/theorems/aac1ebd0-ef55-455f-aac8-58ca726b1184
-- title:
--   A complete irredundant list of the $65$ Sohncke space-group types
-- statement:
--   Work in $E=\mathbb R^3$ with its Euclidean metric, and let $\mathrm{Isom}(E)$ be the group of bijective affine isometries of $E$. Call a subgroup $G\le\mathrm{Isom}(E)$ *crystallographic* if (i) for every $x\in E$ and every $\varepsilon>0$ the set $\{g\in G:\operatorname{dist}(g(x),x)\le\varepsilon\}$ is finite, and (ii) there are three linearly independent vectors $v_1,v_2,v_3$ such that translation by each $v_i$ belongs to $G$.
--
--   For subgroups $G_1,G_2\le\mathrm{Isom}(E)$ write $G_1\sim G_2$ (*affinely equivalent*) if some invertible affine map $\varphi$ of $E$ satisfies $\varphi G_1\varphi^{-1}=G_2$ as sets of affine maps, and $G_1\sim_{+}G_2$ (*orientation-preserving affinely equivalent*) if such a $\varphi$ can be chosen with $\det(\varphi_{\mathrm{lin}})>0$.
--
--   Call a crystallographic group $G$ a *Sohncke group* if every $g\in G$ has $\det(g_{\mathrm{lin}})>0$, that is, if $G$ consists entirely of orientation-preserving isometries. Note that this restricts the groups themselves, not the maps used to compare them.
--
--   This statement is the enumeration form of the count of $65$ Sohncke types: there is a list
--
--   $$
--   G_1,\dots,G_{65}
--   $$
--
--   of Sohncke crystallographic groups in $\mathbb R^3$ that is
--
--   1. **complete**: every Sohncke crystallographic group $G$ satisfies $G_i\sim_{+}G$ for some index $i$; and
--   2. **irredundant**: $G_i\sim_{+}G_j$ forces $i=j$.
--
--   Thus the Sohncke groups fall into exactly $65$ classes under orientation-preserving affine conjugacy — the $65$ chiral space-group types among the $230$.
--
--   **Formalization Note.** The groups range over the subtype of `CrystallographicGroup 3` whose every element satisfies `IsOrientationPreservingIsom`, and the comparison is `AffOPEquivalent` applied to the underlying subgroups; both predicates are taken verbatim from the LeanEval definition bundle.
-- source:
--   LeanEval v1, problem space_groups_230; LeanEval/Geometry/SpaceGroups.lean, LeanEval.Geometry.SpaceGroupsProblem.space_groups, repository commit 296b7491ec989d21bcf8636a9a69231a1e5d1d25: https://github.com/leanprover/lean-eval/blob/296b7491ec989d21bcf8636a9a69231a1e5d1d25/LeanEval/Geometry/SpaceGroups.lean . Classification due to E. S. Fedorov (1891) and A. Schoenflies (1891), independently; background: Oliver Knill, Some Fundamental Theorems in Mathematics, section 94 (Crystallography), printed p. 41, https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf .

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem

theorem space_groups_sohncke_classification :
    ∃ f : Fin 65 →
        { G : CrystallographicGroup 3 // ∀ g, g ∈ G.1 → IsOrientationPreservingIsom g },
      (∀ G : { G : CrystallographicGroup 3 // ∀ g, g ∈ G.1 → IsOrientationPreservingIsom g },
          ∃ i : Fin 65, AffOPEquivalent (f i).1.1 G.1.1) ∧
        (∀ i j : Fin 65, AffOPEquivalent (f i).1.1 (f j).1.1 → i = j) := by
  sorry

end SpaceGroupsProblem
end Geometry
end LeanEval
