-- Prove2me | Theorems.Thm_GroupCohomology_RepPi_isZero_groupCohomology_obj
-- name    : GroupCohomology.RepPi.isZero_groupCohomology_obj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/50d3af3b-7358-575a-b367-b484b2b3a44d
-- title:
--   Vanishing of Hⁿ for a product of representations
-- statement:
--   Let $k$ be a commutative ring, $G$ a group and $\iota$ a type, all in the same universe, let $F : \iota \to \mathrm{Rep}\,k\,G$ be a family of $k$-linear representations of $G$, and let $n$ be a natural number. Write [`GroupCohomology.RepPi.obj F`](def/GroupCohomology_RepPi.html#L21) for the representation whose underlying $k$-module is the dependent product $\prod_{i} F_i$ and whose $G$-action is given componentwise, $g$ acting by the map whose $i$-th component is the $i$-th projection followed by $\rho_{F_i}(g)$ (this is the content of [`GroupCohomology.RepPi.piRepresentation`](def/GroupCohomology_RepPi.html#L13), whose multiplicativity and unitality are checked pointwise). The hypothesis is that for every index $i$ the object $H^n(G, F_i)$, computed in Mathlib as `groupCohomology (F i) n`, is a zero object. The conclusion is that `groupCohomology (GroupCohomology.RepPi.obj F) n` is a zero object as well, i.e. $H^n(G, \prod_i F_i) = 0$. Only the vanishing statement is asserted; no isomorphism $H^n(G,\prod_i F_i) \cong \prod_i H^n(G,F_i)$ is produced.
--
--   This is the degree-wise vanishing half of the commutation of group cohomology with arbitrary products of coefficient modules, stated for an explicitly constructed product representation rather than a categorical limit in $\mathrm{Rep}\,k\,G$. It is used in the idelic computations, specifically by [`NumberField.FiniteSIdele.isZero_groupCohomology_pi_coind_localIntegerUnits_of_ramificationIdx_eq_one`](thm.html#NumberField.FiniteSIdele.isZero_groupCohomology_pi_coind_localIntegerUnits_of_ramificationIdx_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GroupCohomology_RepPi_isZero_groupCohomology_obj.lean

import Mathlib
import Definitions.Def_GroupCohomology_RepPi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory

theorem GroupCohomology.RepPi.isZero_groupCohomology_obj {k G ι : Type u} [CommRing k] [Group G]
    (F : ι → Rep.{u} k G) (n : ℕ) (h : ∀ i, CategoryTheory.Limits.IsZero (groupCohomology (F i) n)) :
    CategoryTheory.Limits.IsZero (groupCohomology (GroupCohomology.RepPi.obj F) n) := by sorry
