-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_genusFF_xHFunctionFieldC_levelH_eq_of_eq_two
-- name    : ModularCurve.FullLevel.genusFF_xHFunctionFieldC_levelH_eq_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/7da25cce-f44c-533c-8a4e-d9386d50029a
-- title:
--   Characteristic-2 genus of the Γ_H(4M') q-expansion field
-- statement:
--   Let $q$ be a prime with $q = 2$, let $M'$ be a non-zero natural number not divisible by $q$, and let $\kappa$ be an algebraically closed field of characteristic $q$. Let $H =$ `levelH q M'` be the kernel of the reduction map $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$ on units, and let `xHFunctionFieldC κ (q ^ 2 * M') H` be the intermediate field of the Laurent series field $\kappa((q))$ obtained by adjoining to $\kappa$ the family `intFormRatiosC` attached to the congruence subgroup [`CohCarrier.GammaH (q ^ 2 * M') H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image under the inclusion of $\Gamma_0(q^2M')$ of the preimage of $H$ under `gamma0Units`. The assertion is that the genus of this field over $\kappa$, defined as $\dim_\kappa H^1$ of the zero divisor in the group $\mathrm{Place}(\kappa, \cdot) \to_{\mathrm{f}} \mathbb{Z}$ of divisors, equals, as a rational number, $$1 + \frac{\psi(M')}{12} - \frac{\nu_2(M')}{4} - \frac{\nu_3(M')}{3} - \frac{c(M')}{2},$$ where $\psi(M') = \sum_{d \mid M',\ d \text{ squarefree}} M'/d$, $\nu_2(M')$ and $\nu_3(M')$ count the solutions of $x^2 + 1 = 0$ and of $x^2 + x + 1 = 0$ in $\mathbb{Z}/M'$, and $c(M') = \sum_{d \mid M'} \varphi(\gcd(d, M'/d))$.
--
--   The right-hand side is the usual genus formula for $X_0(M')$; the content is that in characteristic $2$ the Igusa-type level structure at $q = 2$ contributes nothing, because $(\mathbb{Z}/2)^\times$ is trivial and the level-$\Gamma_H(4M')$ $q$-expansion field collapses to the level-$M'$ modular function field over $\kappa$. It feeds the genus comparison used in the characteristic-$2$ supersingular-chart count, [`ModularCurve.FullLevel.genusFF_fieldBar_add_eq_of_igusa_supersingular_charts_of_eq_two_of_dvd`](thm.html#ModularCurve.FullLevel.genusFF_fieldBar_add_eq_of_igusa_supersingular_charts_of_eq_two_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_genusFF_xHFunctionFieldC_levelH_eq_of_eq_two.lean

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel

theorem ModularCurve.FullLevel.genusFF_xHFunctionFieldC_levelH_eq_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] :
    (AlgebraicCurve.genusFF κ ↥(xHFunctionFieldC κ (q ^ 2 * M') (levelH q M')) : ℚ) = genusFormula M' := by sorry
