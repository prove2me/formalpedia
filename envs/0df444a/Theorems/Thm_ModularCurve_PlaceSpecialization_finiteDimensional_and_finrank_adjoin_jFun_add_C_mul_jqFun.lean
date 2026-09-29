-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun
-- name    : ModularCurve.PlaceSpecialization.finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/7ffd2714-0e85-5588-9fba-72d2eae81c57
-- title:
--   Degree 2q of the pencil j + c j_q on X₀(q)
-- statement:
--   Let $q$ be a prime and let $c$ be a non-zero element of $\overline{\mathbb Q}$ (realised as `AlgebraicClosure ℚ`). Work inside $F =$ `modularFunctionFieldBar (1 * q)`, the subfield of the Laurent series field $\overline{\mathbb Q}((\mathfrak q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of the full modular function field of level $1\cdot q$ over $\mathbb Q$. In $F$ consider the two elements `PlaceSpecialization.jFun`, the image of the $\mathfrak q$-expansion $j(\mathfrak q)$, and `PlaceSpecialization.jqFun`, the image of the series obtained from $j(\mathfrak q)$ by multiplying all exponents by $1\cdot q$, i.e. $j(\mathfrak q^{q})$. Write $L = \overline{\mathbb Q}\bigl(j + c\,j_q\bigr)$ for the intermediate field of $F/\overline{\mathbb Q}$ obtained by adjoining the single element $j + c\,j_q$, where $c$ acts through the structure map $\overline{\mathbb Q} \to F$. The assertion is twofold: $F$ is finite-dimensional as an $L$-vector space, and its rank over $L$ equals $2q$.
--
--   This computes the degree of the map $X_0(q) \to \mathbb P^1$ given by the pencil member $j + c\,j_q$ with $c \neq 0$: the function has poles only at the two cusps, of order $q$ at each, so the degree is $2q$ (for $c = 0$ the degree would be the index $q+1$ of the $j$-line instead). It is used in the analysis of prolongation pairs above a place specialization, namely by [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.integers_eq_or_eq_of_forall_mem_iff_pencil`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.integers_eq_or_eq_of_forall_mem_iff_pencil) and [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_filter_value_eq_sum_roots_add_pencil`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_filter_value_eq_sum_roots_add_pencil).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.finiteDimensional_and_finrank_adjoin_jFun_add_C_mul_jqFun
    {q : ℕ} [Fact q.Prime] (c : AlgebraicClosure ℚ) (hc : c ≠ 0) :
    FiniteDimensional
        ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({PlaceSpecialization.jFun (q := q)
              + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c
                * PlaceSpecialization.jqFun (q := q)} : Set ↥(modularFunctionFieldBar (1 * q))))
        ↥(modularFunctionFieldBar (1 * q))
      ∧ Module.finrank
          ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({PlaceSpecialization.jFun (q := q)
                + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c
                  * PlaceSpecialization.jqFun (q := q)} : Set ↥(modularFunctionFieldBar (1 * q))))
          ↥(modularFunctionFieldBar (1 * q)) = 2 * q := by sorry
