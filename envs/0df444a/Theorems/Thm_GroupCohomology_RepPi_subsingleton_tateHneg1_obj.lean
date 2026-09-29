-- Prove2me | Theorems.Thm_GroupCohomology_RepPi_subsingleton_tateHneg1_obj
-- name    : GroupCohomology.RepPi.subsingleton_tateHneg1_obj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/432c8c50-d807-5a86-894a-9f3300133a6b
-- title:
--   Factorwise vanishing of ̂ H⁻¹ passes to products
-- statement:
--   Let $k$ be a commutative ring, $G$ a group with finitely many elements, and $\iota$ a type (all three in the same universe), and let $F : \iota \to \mathrm{Rep}\,k\,G$ be a family of $k$-linear representations of $G$. For a representation $\rho$ on $V$, write $\rho.\mathrm{tateHneg1}$ for the kernel of the map $\mathrm{normBar} : V_G \to V^G$ from the coinvariants to the invariants induced by the norm $\sum_{g \in G} \rho(g)$ (the map on coinvariants obtained from $v \mapsto \sum_g \rho(g)v$, which kills the augmentation submodule); for an object $A$ of $\mathrm{Rep}\,k\,G$ this is applied to $A.\rho$. The hypothesis is that for every $i$ the $k$-module $(F\,i).\mathrm{tateHneg1}$ is a subsingleton, i.e. has at most one element. The conclusion is that $(\mathrm{GroupCohomology.RepPi.obj}\,F).\mathrm{tateHneg1}$ is a subsingleton, where $\mathrm{GroupCohomology.RepPi.obj}\,F$ is the representation on the product module $\prod_{i} F\,i$ on which $g \in G$ acts componentwise by $(F\,i).\rho(g)$ in the $i$-th coordinate.
--
--   This is the statement that Tate cohomology in degree $-1$ of a (possibly infinite) direct product of $G$-modules vanishes as soon as it vanishes in each factor, phrased as a subsingleton assertion so that consumers never have to manipulate the product of the individual Tate groups. It is used for the Tate cohomology of archimedean and finite $S$-idèle modules, whose local factors have vanishing $\hat H^{-1}$, in [`NumberField.ArchIdele.card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1`](thm.html#NumberField.ArchIdele.card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1) and [`NumberField.FiniteSIdele.card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1`](thm.html#NumberField.FiniteSIdele.card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GroupCohomology_RepPi_subsingleton_tateHneg1_obj.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_RepPi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem GroupCohomology.RepPi.subsingleton_tateHneg1_obj {k G ι : Type u} [CommRing k] [Group G] [Fintype G]
    (F : ι → Rep.{u} k G) (h : ∀ i, Subsingleton (F i).tateHneg1) :
    Subsingleton (GroupCohomology.RepPi.obj F).tateHneg1 := by sorry
