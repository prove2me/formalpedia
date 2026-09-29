-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three
-- name    : ModularCurve.FullLevel.xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/2430d2e8-827c-5860-a515-18db0ab0b845
-- title:
--   In characteristic 3, the Igusa-level q-expansion field is κ(X₀(M'))
-- statement:
--   Let $q$ be a prime subject to the hypothesis $q = 3$ (the prime is kept as a variable), let $M'$ be a nonzero natural number with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ satisfying `LiesOverPrime q`, i.e. the image of $q$ in $\overline{\mathbb Q}$ is a non-unit of $A$; write $\kappa$ for the residue field of $A$. Put $H =$ `levelH q M'`, the kernel of the reduction map $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$, that is the units of $\mathbb Z/q^2M'$ congruent to $1$ modulo $q$, and let $\Gamma_H(q^2M') \le \mathrm{SL}(2,\mathbb Z)$ be the subgroup obtained as the image in $\mathrm{SL}(2,\mathbb Z)$ of the preimage of $H$ under the unit character `gamma0Units` of $\Gamma_0(q^2M')$. The assertion is an equality of intermediate fields of the Laurent series field $\kappa((q))$ over $\kappa$: the field generated over $\kappa$ by the set `intFormRatiosC` attached to $\kappa$ and $\Gamma_H(q^2M')$ coincides with the field generated over $\kappa$ by the two Laurent series `jqModC` $\kappa$ and `jqNModC` $\kappa$ $M'$, namely the reduced $q$-expansion $\bar j$ of the modular invariant and its substitution $q \mapsto q^{M'}$.
--
--   This identifies the residue field at the cusp $\infty$ of the $\Gamma_H(q^2M')$-level $q$-expansion field in characteristic $3$ with the function field $\kappa(X_0(M'))$, so that for $q = 3$ the relevant Igusa component carries no extra Kummer generator, in contrast with the case $q \ge 5$. It feeds the subsequent characteristic-$3$ results on places, integral structures and descent for the full-level curve over $X_0(M')$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three.lean

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_IgusaFunctionField
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped ArithmeticFunction.sigma

theorem ModularCurve.FullLevel.xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') =
      ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) M' := by sorry
