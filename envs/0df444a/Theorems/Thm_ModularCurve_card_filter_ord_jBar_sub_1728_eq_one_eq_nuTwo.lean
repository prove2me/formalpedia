-- Prove2me | Theorems.Thm_ModularCurve_card_filter_ord_jBar_sub_1728_eq_one_eq_nuTwo
-- name    : ModularCurve.card_filter_ord_jBar_sub_1728_eq_one_eq_nuTwo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/45d44ba1-aaf3-5237-9f09-4f7ec110680b
-- title:
--   Unramified places over j=1728 at odd prime level count ν₂(p)
-- statement:
--   Let $p$ be a prime with $p$ odd. Work with the field $F =$ [`ModularCurve.modularFunctionFieldBar p`](def/ModularCurve_ArithmeticGalois.html#L111), the intermediate field of $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ over $\overline{\mathbb Q}$ obtained by adjoining the coefficientwise images, under the map induced by $\mathbb Q \to \overline{\mathbb Q}$, of the full modular function field of level $p$ (itself generated over $\mathbb Q$ by the divisor expansions of level $p$), and with the element [`ModularCurve.jBar p`](def/ModularCurve_MazurStepThreeInputs.html#L43) of $F$ given by the $q$-expansion of the modular invariant with coefficients in $\overline{\mathbb Q}$. A place of $F$ over $\overline{\mathbb Q}$ is a valuation subring of $F$ containing $\overline{\mathbb Q}$, distinct from $F$ itself, whose ring is a principal ideal ring, and $v.\mathrm{ord}$ denotes the associated normalised integer valuation. Let $S_1$ be a finite set of such places such that a place $v$ lies in $S_1$ precisely when $v.\mathrm{ord}(\bar\jmath - 1728) > 0$, where $1728$ is the image of $1728 \in \overline{\mathbb Q}$ under the structure map. Then the number of $v \in S_1$ with $v.\mathrm{ord}(\bar\jmath - 1728) = 1$ equals [`ModularCurve.nuTwo p`](def/ModularCurve_GenusNumerics.html#L9), that is, the cardinality of $\{x \in \mathbb Z/p : x^2 + 1 = 0\}$.
--
--   Classically this identifies, for odd prime level, the number of points of $X_0(p)$ over $\overline{\mathbb Q}$ lying above $j = 1728$ at which the $j$-map is unramified with the number $\nu_2(p)$ of elliptic points of order $2$ of $\Gamma_0(p)$. It supplies one of the ramification counts fed into the Riemann–Hurwitz computation of the genus of $X_0(p)$, and is cited by [`ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula_of_prime`](thm.html#ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_card_filter_ord_jBar_sub_1728_eq_one_eq_nuTwo.lean

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.card_filter_ord_jBar_sub_1728_eq_one_eq_nuTwo (p : ℕ) [Fact p.Prime] (hodd : Odd p)
    (S1 : Finset (AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar p)))
    (hS1 : ∀ v, v ∈ S1 ↔ 0 < v.ord (ModularCurve.jBar p - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar p) 1728)) :
    (S1.filter fun v => v.ord (ModularCurve.jBar p - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar p) 1728) = 1).card
      = ModularCurve.nuTwo p := by sorry
