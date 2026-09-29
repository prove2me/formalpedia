-- Prove2me | Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_space_groups_master_classification
-- name    : LeanEval.Geometry.SpaceGroupsProblem.space_groups_master_classification
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-06T08:40:23.96906+00:00
-- url     : https://prove2.me/theorems/855f752e-313b-4ee8-b438-09146d920ec2
-- title:
--   Master enumeration of the space groups of $\mathbb R^3$: the list of $230$ with its affine and Sohncke bookkeeping
-- statement:
--   Work in $E=\mathbb R^3$ with its Euclidean metric and let $\mathrm{Isom}(E)$ be the group of bijective affine isometries. A subgroup $G\le\mathrm{Isom}(E)$ is *crystallographic* if (i) for every $x\in E$ and every $\varepsilon>0$ the set $\{g\in G:\operatorname{dist}(g(x),x)\le\varepsilon\}$ is finite, and (ii) $G$ contains translations by three linearly independent vectors. Write $G_1\sim G_2$ if $\varphi G_1\varphi^{-1}=G_2$ for some invertible affine map $\varphi$, and $G_1\sim_{+}G_2$ if such a $\varphi$ can be chosen with $\det(\varphi_{\mathrm{lin}})>0$. Call $G$ a *Sohncke group* if every $g\in G$ has $\det(g_{\mathrm{lin}})>0$.
--
--   The three classical counts — $230$ space-group types, $219$ affine classes, $65$ Sohncke types — are three readings of one and the same classification, and this statement packages them into a single assertion. It asks for a list
--
--   $$G_1,\dots,G_{230}$$
--
--   of crystallographic groups of $\mathbb R^3$ together with two pieces of bookkeeping data about that list:
--
--   1. **The list is a complete irredundant set of representatives for $\sim_{+}$.** Every crystallographic group $G$ satisfies $G_i\sim_{+}G$ for some $i$, and $G_i\sim_{+}G_j$ forces $i=j$. This is the Fedorov–Schoenflies count of $230$.
--
--   2. **A selection $s:\{1,\dots,219\}\to\{1,\dots,230\}$ of representatives for $\sim$.** Every index $i$ satisfies $G_{s(k)}\sim G_i$ for some $k$, and $G_{s(k)}\sim G_{s(l)}$ forces $k=l$. Since $\sim$ is coarser than $\sim_{+}$, and every crystallographic group is $\sim_{+}$-equivalent (hence $\sim$-equivalent) to some member of the list, the $219$ selected members form a complete irredundant list for $\sim$: the $11$ enantiomorphic pairs among the $230$ have been merged.
--
--   3. **An injection $t:\{1,\dots,65\}\to\{1,\dots,230\}$ whose image is exactly the set of Sohncke members of the list**, i.e. $G_i$ is a Sohncke group if and only if $i=t(k)$ for some $k$. Because the Sohncke condition is invariant under affine conjugacy, the Sohncke groups form a union of $\sim_{+}$-classes, so these $65$ members form a complete irredundant list of the Sohncke groups up to $\sim_{+}$.
--
--   Consequently this single statement implies each of `space_groups_OP_classification` ($230$), `space_groups_affine_classification` ($219$) and `space_groups_sohncke_classification` ($65$); those three deductions are supplied as proof-sketch reductions to this theorem, so the mission's frontier is the present statement alone.
--
--   **Formalization note.** `CrystallographicGroup 3` is the subtype of crystallographic subgroups, `AffOPEquivalent` and `AffinelyEquivalent` are $\sim_{+}$ and $\sim$, and `IsOrientationPreservingIsom g` says $\det(g_{\mathrm{lin}})>0$; all are the mission's own definitions.
-- source:
--   Fedorov (1891) / Schoenflies (1891); see e.g. Hahn (ed.), International Tables for Crystallography, Vol. A, Table 1.4.1 (230 space-group types, 219 affine classes, 65 Sohncke types)

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions

namespace LeanEval
namespace Geometry
namespace SpaceGroupsProblem

theorem space_groups_master_classification :
    ∃ f : Fin 230 → CrystallographicGroup 3,
      (∀ G : CrystallographicGroup 3, ∃ i : Fin 230, AffOPEquivalent (f i).1 G.1) ∧
      (∀ i j : Fin 230, AffOPEquivalent (f i).1 (f j).1 → i = j) ∧
      (∃ s : Fin 219 → Fin 230,
        (∀ i : Fin 230, ∃ k : Fin 219, AffinelyEquivalent (f (s k)).1 (f i).1) ∧
        (∀ k l : Fin 219, AffinelyEquivalent (f (s k)).1 (f (s l)).1 → k = l)) ∧
      (∃ t : Fin 65 → Fin 230, Function.Injective t ∧
        ∀ i : Fin 230,
          (∀ g, g ∈ (f i).1 → IsOrientationPreservingIsom g) ↔ ∃ k : Fin 65, t k = i) := by
  sorry

end SpaceGroupsProblem
end Geometry
end LeanEval
