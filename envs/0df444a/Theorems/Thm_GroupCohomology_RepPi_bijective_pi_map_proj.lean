-- Prove2me | Theorems.Thm_GroupCohomology_RepPi_bijective_pi_map_proj
-- name    : GroupCohomology.RepPi.bijective_pi_map_proj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/3fa81af4-d8b6-55ac-9d0e-d981f87f494e
-- title:
--   Cohomology commutes with products of representations
-- statement:
--   Let $k$ be a commutative ring, $G$ a group and $\iota$ an index type, and let $F : \iota \to \mathrm{Rep}\,k\,G$ be a family of $k$-linear representations of $G$. Write [`GroupCohomology.RepPi.obj F`](def/GroupCohomology_RepPi.html#L21) for the representation of $G$ on the product module $\prod_{i} F_i$ whose action of $g$ is the linear map sending $x$ to the tuple $((F_i).\rho\,g\,(x_i))_i$, i.e. the componentwise action obtained from the projections, and for each $i$ let [`GroupCohomology.RepPi.proj F i : obj F ⟶ F i`](def/GroupCohomology_RepPi.html#L25) be the morphism of representations whose underlying linear map is the $i$-th projection (which commutes with the actions by construction). Then for every natural number $n$ the map
--   $$H^n\bigl(G, \textstyle\prod_i F_i\bigr) \longrightarrow \prod_i H^n(G, F_i),\qquad x \longmapsto \bigl(\mathrm{groupCohomology.map}(\mathrm{id}_G, \mathrm{proj}\,F\,i, n)(x)\bigr)_{i \in \iota},$$
--   whose $i$-th component is the map induced on degree-$n$ group cohomology by the identity homomorphism of $G$ together with the $i$-th projection, is bijective as a function. The assertion is bijectivity of the underlying function; that the map is $k$-linear is not part of the statement.
--
--   This is the statement that group cohomology in each fixed degree commutes with arbitrary products of coefficient modules, in the concrete form needed for the explicit product representation [`GroupCohomology.RepPi.obj`](def/GroupCohomology_RepPi.html#L21): inhomogeneous cochains valued in a product are exactly tuples of cochains. It is used in the idelic cohomology computations, namely by [`NumberField.SIdele.bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one`](thm.html#NumberField.SIdele.bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one), to identify the cohomology of a product of local coefficient modules with the product of the local cohomology groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GroupCohomology_RepPi_bijective_pi_map_proj.lean

import Mathlib
import Definitions.Def_GroupCohomology_RepPi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory

theorem GroupCohomology.RepPi.bijective_pi_map_proj {k G : Type} [CommRing k] [Group G] {ι : Type}
    (F : ι → Rep k G) (n : ℕ) :
    Function.Bijective (fun x : groupCohomology (GroupCohomology.RepPi.obj F) n =>
      fun i : ι => (groupCohomology.map (MonoidHom.id G) (GroupCohomology.RepPi.proj F i) n).hom x) := by sorry
