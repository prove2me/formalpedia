-- Prove2me | Theorems.Thm_ModularCurve_card_filter_ord_jBar_eq_one_eq_nuThree
-- name    : ModularCurve.card_filter_ord_jBar_eq_one_eq_nuThree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/b95b0ccf-e56f-57d5-8028-967ffa4bd9d7
-- title:
--   Unramified points above j=0 on X₀(p) count ν₃(p)
-- statement:
--   Let $p$ be a prime which is in addition odd. Work with the field $\overline{\mathbb Q}F_p$ = [`ModularCurve.modularFunctionFieldBar p`](def/ModularCurve_ArithmeticGalois.html#L111), the intermediate field of $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ over $\overline{\mathbb Q}$ obtained by adjoining to $\overline{\mathbb Q}$ the image, under coefficientwise extension of scalars along $\mathbb Q \to \overline{\mathbb Q}$, of the field [`ModularCurve.modularFunctionFieldFull p`](def/ModularCurve_X0.html#L305) (itself the subfield of $\mathrm{LaurentSeries}(\mathbb Q)$ generated over $\mathbb Q$ by the divisor expansions at level $p$). A place of this field over $\overline{\mathbb Q}$ is, by definition, a valuation subring containing the image of $\overline{\mathbb Q}$, different from the whole field, and a principal ideal ring; for such a $v$, $v.\mathrm{ord}$ is minus the logarithm of the associated $\mathbb Z^{m0}$-valued adic valuation. Let $S_0$ be a finite set of such places, assumed to consist of exactly those places $v$ with $v.\mathrm{ord}(\bar\jmath_p) > 0$, where $\bar\jmath_p$ = [`ModularCurve.jBar p`](def/ModularCurve_MazurStepThreeInputs.html#L43) is the element of $\overline{\mathbb Q}F_p$ given by the $q$-expansion of the modular invariant with coefficients pushed into $\overline{\mathbb Q}$. Then the number of $v \in S_0$ with $v.\mathrm{ord}(\bar\jmath_p) = 1$ equals $\nu_3(p) = \#\{x \in \mathbb Z/p : x^2 + x + 1 = 0\}$.
--
--   Classically: among the points of $X_0(p)$ over $\overline{\mathbb Q}$ lying above $j = 0$, those at which the $j$-map is unramified are precisely the elliptic points of order $3$ of $\Gamma_0(p)$, and there are $\nu_3(p)$ of them. The statement supplies the $\varepsilon_3$-term in the ramification bookkeeping used by [`ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula_of_prime`](thm.html#ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_card_filter_ord_jBar_eq_one_eq_nuThree.lean

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.card_filter_ord_jBar_eq_one_eq_nuThree (p : ℕ) [Fact p.Prime] (hodd : Odd p)
    (S0 : Finset (AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar p)))
    (hS0 : ∀ v, v ∈ S0 ↔ 0 < v.ord (ModularCurve.jBar p)) :
    (S0.filter fun v => v.ord (ModularCurve.jBar p) = 1).card = ModularCurve.nuThree p := by sorry
