-- Prove2me | Theorems.Thm_GroupCohomology_RepPi_nonempty_tateHneg1_obj_linearEquiv
-- name    : GroupCohomology.RepPi.nonempty_tateHneg1_obj_linearEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/2325e524-b876-53ff-b24a-38098fa829eb
-- title:
--   ̂ H⁻¹ of a product of representations splits
-- statement:
--   Let $k$ be a commutative ring, $G$ a group with finitely many elements, $\iota$ a type (all three in the same universe), and let $F : \iota \to \mathrm{Rep}\,k\,G$ be a family of $k$-linear representations of $G$. Write $\mathrm{obj}\,F$ for the representation of $G$ on the product module $\prod_{i}F_i$ with $g$ acting componentwise by $\rho_{F_i}(g)$, i.e. `Rep.of (piRepresentation F)`. For a representation $\rho$ on $V$, `tateHneg1` denotes the kernel of the map $\bar N \colon V_G \to V^G$ induced on coinvariants by the norm $\sum_{g \in G}\rho(g)$ (well defined since $G$ is finite), that is, Tate's $\hat H^{-1}$. The assertion is that the type of $k$-linear isomorphisms
--   $$\hat H^{-1}\bigl(\mathrm{obj}\,F\bigr) \;\simeq_k\; \prod_{i \in \iota} \hat H^{-1}(F_i)$$
--   is nonempty; only the existence of such an isomorphism is asserted, no particular comparison map being named in the statement, and no naturality in $F$ being claimed.
--
--   This is the statement that Tate cohomology in degree $-1$ commutes with arbitrary products of representations of a finite group, the finiteness of $G$ being what makes the augmentation submodule of a product equal to the product of the augmentation submodules. It is used by [`GroupCohomology.RepPi.subsingleton_tateHneg1_obj`](thm.html#GroupCohomology.RepPi.subsingleton_tateHneg1_obj), which deduces vanishing of $\hat H^{-1}$ of a product from vanishing in each factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GroupCohomology_RepPi_nonempty_tateHneg1_obj_linearEquiv.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_RepPi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem GroupCohomology.RepPi.nonempty_tateHneg1_obj_linearEquiv {k G ι : Type u} [CommRing k] [Group G] [Fintype G]
    (F : ι → Rep.{u} k G) :
    Nonempty ((GroupCohomology.RepPi.obj F).tateHneg1 ≃ₗ[k] ((i : ι) → (F i).tateHneg1)) := by sorry
