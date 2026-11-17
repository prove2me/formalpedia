-- Prove2me | Theorems.Thm_N25_gamma0_field_degree
-- name    : N25.gamma0_field_degree
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:02.0352+00:00
-- url     : https://prove2.me/theorems/51de43d4-0c02-4e1f-9991-903246889d19
-- title:
--   The level-$25$ character field has degree $5$ over the $\Gamma_0(25)$ field
-- statement:
--   Let $F_0$ be the base change to $\overline{\mathbb Q}$ of the modular function field for $\Gamma_0(25)$, and let $F$ be the geometric function field for the subgroup $H_{25}$. Then $F_0$ is an intermediate field of $F$ and
--
--   $$[F:F_0]=5.$$
--
--   This identifies the distinguished diamond symmetry as the degree-five extension over the genus-zero base field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero
import Theorems.Thm_ModularCurve_relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le

set_option autoImplicit false
open N25

theorem N25.gamma0_field_degree :
    let F₀ := ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
      (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 25))
    let F := ModularCurve.xHFunctionFieldBar 25 H25
    F₀ ≤ F ∧ F₀.relfinrank F = 5 := by sorry
