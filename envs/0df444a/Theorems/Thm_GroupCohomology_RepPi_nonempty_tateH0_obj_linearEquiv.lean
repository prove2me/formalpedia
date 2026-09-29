-- Prove2me | Theorems.Thm_GroupCohomology_RepPi_nonempty_tateH0_obj_linearEquiv
-- name    : GroupCohomology.RepPi.nonempty_tateH0_obj_linearEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/56d94cd2-aae9-54d5-a3c5-4a66814e7674
-- title:
--   Tate ̂ H⁰ of a product of representations
-- statement:
--   Let $k$ be a commutative ring, $G$ a finite group and $\iota$ a type, all in the same universe, and let $F : \iota \to \mathrm{Rep}\,k\,G$ be a family of $k$-linear representations of $G$. Write $P$ for the product representation [`GroupCohomology.RepPi.obj F`](def/GroupCohomology_RepPi.html#L21): its underlying module is the dependent product $\prod_i F_i$ and $g \in G$ acts componentwise by $(g \cdot x)_i = (F_i).\rho(g)(x_i)$. For a representation with carrier $V$ and action $\rho$, the Tate object `tateH0` is by definition the quotient $V^G / \operatorname{range}(\bar N_\rho)$, where $\bar N_\rho : V_G \to V^G$ is the map induced on coinvariants by the norm $x \mapsto \sum_{g \in G} \rho(g)x$, which lands in the invariants and kills the augmentation submodule. The theorem asserts that the type of $k$-linear equivalences $$\bigl(\textstyle\prod_i F_i\bigr)^G / \operatorname{range}(\bar N_P) \;\simeq\; \prod_i \bigl(F_i^G / \operatorname{range}(\bar N_{(F_i).\rho})\bigr)$$ is nonempty; that is, such an isomorphism exists, no particular one being named in the statement.
--
--   This is the additivity of Tate cohomology in degree $0$ over an arbitrary index set, for the explicit model $V^G/N_G V$ of $\hat H^0$. It is used to compute $\hat H^0$ of product representations, for instance by [`GroupCohomology.RepPi.natCard_tateH0_obj_eq_prod_of_subsingleton`](thm.html#GroupCohomology.RepPi.natCard_tateH0_obj_eq_prod_of_subsingleton).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GroupCohomology_RepPi_nonempty_tateH0_obj_linearEquiv.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_RepPi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem GroupCohomology.RepPi.nonempty_tateH0_obj_linearEquiv {k G ι : Type u} [CommRing k] [Group G] [Fintype G]
    (F : ι → Rep.{u} k G) :
    Nonempty ((GroupCohomology.RepPi.obj F).tateH0 ≃ₗ[k] ((i : ι) → (F i).tateH0)) := by sorry
