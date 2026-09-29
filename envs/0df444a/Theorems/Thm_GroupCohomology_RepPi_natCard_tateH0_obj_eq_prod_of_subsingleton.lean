-- Prove2me | Theorems.Thm_GroupCohomology_RepPi_natCard_tateH0_obj_eq_prod_of_subsingleton
-- name    : GroupCohomology.RepPi.natCard_tateH0_obj_eq_prod_of_subsingleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/f5e75c5c-7e59-50fa-803e-6786fab9f520
-- title:
--   Order of Tate ̂ H⁰ of a product representation
-- statement:
--   Let $k$ be a commutative ring, $G$ a finite group and $\iota$ a type (all in one universe), let $F : \iota \to \mathrm{Rep}\,k\,G$ be a family of $k$-linear representations of $G$, and let $s$ be a finite subset of $\iota$. Here, for a representation with underlying $k$-module $V$ and action $\rho$, the group `tateH0` is the quotient of the invariants $V^{G}$ by the image of the map induced on coinvariants by the norm $\sum_{g \in G} \rho(g)$, i.e. the Tate group $\hat H^{0}(G, V)$; and [`GroupCohomology.RepPi.obj F`](def/GroupCohomology_RepPi.html#L21) is the representation on the full product $\prod_{i} F_i$ with the componentwise action $(g \cdot x)_i = \rho_{F_i}(g)(x_i)$. Assume that for every $i \notin s$ the group $\hat H^{0}(G, F_i)$ is a subsingleton, that is, trivial. The conclusion is the equality of natural numbers
--   $$\mathrm{Nat.card}\ \hat H^{0}\big(G, \textstyle\prod_i F_i\big) \;=\; \prod_{i \in s} \mathrm{Nat.card}\ \hat H^{0}(G, F_i),$$
--   cardinalities being taken as `Nat.card` (so that an infinite Tate group contributes the value $0$ on either side).
--
--   This is the counting form of the compatibility of Tate cohomology in degree $0$ with arbitrary products of representations: the order of $\hat H^{0}$ of the product equals the finite product of the orders of the factors, once all but finitely many factors have trivial $\hat H^{0}$. It is used in the computation of Herbrand quotients of idèle modules, being cited by the corresponding statements for the archimedean and the finite $S$-idèle families, where the factors outside $S$ are cohomologically trivial; stating it in terms of `Nat.card` lets consumers avoid handling the product type of the Tate groups directly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GroupCohomology_RepPi_natCard_tateH0_obj_eq_prod_of_subsingleton.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_RepPi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem GroupCohomology.RepPi.natCard_tateH0_obj_eq_prod_of_subsingleton {k G ι : Type u} [CommRing k] [Group G] [Fintype G]
    (F : ι → Rep.{u} k G) (s : Finset ι) (h : ∀ i, i ∉ s → Subsingleton (F i).tateH0) :
    Nat.card (GroupCohomology.RepPi.obj F).tateH0 = ∏ i ∈ s, Nat.card (F i).tateH0 := by sorry
