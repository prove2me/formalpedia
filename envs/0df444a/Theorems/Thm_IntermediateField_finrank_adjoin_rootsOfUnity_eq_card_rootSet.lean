-- Prove2me | Theorems.Thm_IntermediateField_finrank_adjoin_rootsOfUnity_eq_card_rootSet
-- name    : IntermediateField.finrank_adjoin_rootsOfUnity_eq_card_rootSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/2b2e087a-40cd-52fd-9da8-8e0f4f7b62e3
-- title:
--   Degree of F(μ_m) equals number of conjugates of ζ₀
-- statement:
--   Let $F$ and $E$ be fields with $E$ an $F$-algebra, $E$ algebraically closed and $F$ of characteristic zero; let $m$ be a natural number with $m>0$, and let $\zeta_0 \in E$ satisfy `IsPrimitiveRoot ζ₀ m`, i.e. $\zeta_0$ is a primitive $m$-th root of unity in $E$. The assertion is an equality of natural numbers: the $F$-dimension, as a module, of the intermediate field $F(\{\zeta \in E : \zeta^m = 1\})$ obtained by adjoining to $F$ inside $E$ all solutions of $\zeta^m = 1$, equals the cardinality of the root set in $E$ of the minimal polynomial of $\zeta_0$ over $F$, that is, the number of elements $t \in E$ with $\mathrm{minpoly}_F(\zeta_0)(t) = 0$ (this root set being finite, its cardinality is taken as a `Fintype.card`). Thus $[F(\mu_m) : F]$ is computed as the number of distinct conjugates of $\zeta_0$ in the algebraically closed field $E$.
--
--   This is the standard degree formula for a cyclotomic extension, in the shape that converts the degree $[F(\mu_m):F]$ into a count of roots of a minimal polynomial. It is a bookkeeping step for degree computations of cyclotomic layers and is cited by [`IntermediateField.finrank_adjoin_rootsOfUnity_padic_eq_orderOf`](thm.html#IntermediateField.finrank_adjoin_rootsOfUnity_padic_eq_orderOf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_finrank_adjoin_rootsOfUnity_eq_card_rootSet.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IntermediateField

theorem IntermediateField.finrank_adjoin_rootsOfUnity_eq_card_rootSet {F E : Type} [Field F] [Field E] [Algebra F E] [IsAlgClosed E] [CharZero F] (m : ℕ) (hm : 0 < m) (ζ₀ : E)
    (hζ₀ : IsPrimitiveRoot ζ₀ m) :
    Module.finrank F (IntermediateField.adjoin F {ζ : E | ζ ^ m = 1})
      = Fintype.card ((minpoly F ζ₀).rootSet E) := by sorry
