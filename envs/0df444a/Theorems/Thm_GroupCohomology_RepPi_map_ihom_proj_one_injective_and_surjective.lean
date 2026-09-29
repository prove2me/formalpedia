-- Prove2me | Theorems.Thm_GroupCohomology_RepPi_map_ihom_proj_one_injective_and_surjective
-- name    : GroupCohomology.RepPi.map_ihom_proj_one_injective_and_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/f0181a3b-7bf7-5b35-aeb8-26601b6057c5
-- title:
--   H¹(G,Hom(R,prod Xᵢ)) is the product of H¹(G,Hom(R,Xᵢ))
-- statement:
--   Let $G$ be a group and $\iota$ a finite type, let $X : \iota \to \mathrm{Rep}\,\mathbb{Z}\,G$ be a family of $\mathbb{Z}[G]$-modules and let $R$ be a $\mathbb{Z}[G]$-module. Write $J =$ [`GroupCohomology.RepPi.obj X`](def/GroupCohomology_RepPi.html#L21) for the representation of $G$ on the product $\prod_{i} X_i$ whose action is componentwise, $g$ acting on a vector by applying $\rho_{X_i}(g)$ in the $i$-th coordinate, and [`GroupCohomology.RepPi.proj X i`](def/GroupCohomology_RepPi.html#L25) for the morphism of representations given by the $i$-th coordinate projection $J \to X_i$. Let $(\mathrm{ihom}\,R)$ denote the internal hom functor on $\mathrm{Rep}\,\mathbb{Z}\,G$, so that $(\mathrm{ihom}\,R).\mathrm{obj}\,Y = \mathrm{Hom}_{\mathbb{Z}}(R,Y)$ with the conjugation action, and let the maps on cohomology be those induced in degree $1$ along the identity of $G$ by $(\mathrm{ihom}\,R)$ applied to the projections. The assertion is the conjunction of two statements about the resulting family of maps $H^1(G,\mathrm{Hom}(R,J)) \to H^1(G,\mathrm{Hom}(R,X_i))$: first, any class $x$ in $H^1(G,\mathrm{Hom}(R,J))$ all of whose images vanish is itself zero; second, any family $(y_i)_i$ with $y_i \in H^1(G,\mathrm{Hom}(R,X_i))$ is realised as the family of images of a single class $x$ in $H^1(G,\mathrm{Hom}(R,J))$. Together these say that the induced map into $\prod_i H^1(G,\mathrm{Hom}(R,X_i))$ is bijective, injectivity being stated in the kernel-trivial form.
--
--   This is the additivity of degree-one group cohomology in the coefficients, in the form needed for internal homs: $\mathrm{Hom}(R,-)$ commutes with products and $H^1(G,-)$ is additive, so $H^1(G,\mathrm{Hom}(R,\prod_i X_i))$ is the product of the $H^1(G,\mathrm{Hom}(R,X_i))$. It is used to assemble place-by-place identifications into a single global statement in [`groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two`](thm.html#groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GroupCohomology_RepPi_map_ihom_proj_one_injective_and_surjective.lean

import Mathlib
import Definitions.Def_GroupCohomology_RepPi
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem GroupCohomology.RepPi.map_ihom_proj_one_injective_and_surjective
    {G : Type} [Group G] {ι : Type} [Finite ι] (X : ι → Rep ℤ G) (R : Rep ℤ G) :
    (∀ x : groupCohomology ((ihom R).obj (GroupCohomology.RepPi.obj X)) 1,
        (∀ i, (groupCohomology.map (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) 1).hom x = 0) → x = 0) ∧
    (∀ y : ∀ i, groupCohomology ((ihom R).obj (X i)) 1,
        ∃ x : groupCohomology ((ihom R).obj (GroupCohomology.RepPi.obj X)) 1,
          ∀ i, (groupCohomology.map (MonoidHom.id G) ((ihom R).map (GroupCohomology.RepPi.proj X i)) 1).hom x = y i) := by sorry
