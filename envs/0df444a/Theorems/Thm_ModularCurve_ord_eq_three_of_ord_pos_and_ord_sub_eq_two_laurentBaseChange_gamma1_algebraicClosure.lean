-- Prove2me | Theorems.Thm_ModularCurve_ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1_algebraicClosure
-- name    : ModularCurve.ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1_algebraicClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/56ee15ee-939b-5cfb-be23-8ce5ba8e581b
-- title:
--   No elliptic points on X₁(M), M ≥ 4, over ℚ̄
-- statement:
--   Fix a natural number $M \ge 4$. Let $F(\Gamma_1(M)) \subseteq \mathbb{Q}((q))$ be [`ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)`](def/ModularCurve_X1.html#L101), the subfield of the field of Laurent series over $\mathbb{Q}$ generated over $\mathbb{Q}$ by all quotients $p_f/p_g$ of $q$-expansions with integral coefficients of two modular forms $f, g$ of one and the same weight $k$ for $\Gamma_1(M)$, the denominator series being nonzero, and let $F$ be [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103) of it to $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, namely the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the image of $F(\Gamma_1(M))$ under the coefficientwise extension of $\mathbb{Q} \to \overline{\mathbb{Q}}$. Let $y \in F$ be an element whose underlying Laurent series is [`ModularCurve.jqModC`](def/ModularCurve_JqCoeff.html#L15), that is $q^{-1}$ times the power series $E_4^3 \cdot \eta^{-24}$-style numerator `jNum` mapped into $\overline{\mathbb{Q}}$, the $q$-expansion of the modular invariant $j$. Let $P$ be a place of $F$ over $\overline{\mathbb{Q}}$, i.e. a valuation subring of $F$ containing $\overline{\mathbb{Q}}$, distinct from $F$ and a principal ideal ring, and let $\operatorname{ord}_P$ be the associated normalised integer-valued order function. Then $\operatorname{ord}_P(y) > 0$ implies $\operatorname{ord}_P(y) = 3$, and $\operatorname{ord}_P(y - 1728) > 0$ implies $\operatorname{ord}_P(y - 1728) = 2$.
--
--   This is the statement that the covering $X_1(M) \to X(1)$ has no elliptic points for $M \ge 4$, so that it is ramified to order exactly $3$ above $j = 0$ and exactly $2$ above $j = 1728$, phrased for places of the $q$-expansion function field after base change of constants to $\overline{\mathbb{Q}}$. It is used to obtain the corresponding ramification statement for the function field over $\mathbb{Q}$ itself, in the computation of the genus and of the divisors of $X_1(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1_algebraicClosure.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1_algebraicClosure
    (M : ℕ) [NeZero M] (hM : 4 ≤ M)
    (y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) :
    (0 < P.ord y → P.ord y = 3) ∧ (0 < P.ord (y - 1728) → P.ord (y - 1728) = 2) := by sorry
