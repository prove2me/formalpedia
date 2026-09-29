-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_genusFF_fieldBar_eq
-- name    : ModularCurve.FullLevel.genusFF_fieldBar_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/1594239a-2c47-56f8-847e-3354fb885bd0
-- title:
--   Genus of the full level-q curve over X₀(M')
-- statement:
--   Let $q$ be a prime with $5 \le q$ and let $M'$ be a nonzero natural number with $q \nmid M'$. Write $H =$ `levelH q M'` for the kernel of the reduction map $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$ induced by $q \mid q^2 M'$, and let $F =$ `fieldBar q M'` be the intermediate field of the Laurent series field over $\overline{\mathbb{Q}}$ obtained from the function field `xHFunctionField` of level $q^2M'$ and subgroup $H$ by the base change `laurentBaseChange` to coefficients in $\overline{\mathbb{Q}}$. The assertion is an identity in $\mathbb{Q}$ between the image of the natural number `genusFF (AlgebraicClosure ℚ) F`, namely the $\overline{\mathbb{Q}}$-dimension of $H^1$ of the zero divisor of $F$ over $\overline{\mathbb{Q}}$, and
--   $$1 + \frac{q(q^2-1)\,\psi(M')}{24} - \frac{(q^2-1)\sum_{d \mid M'} \varphi(\gcd(d, M'/d))}{4},$$
--   where $\psi(M') = \sum_{d \mid M',\ d \text{ squarefree}} M'/d$ is `dedekindPsi M'` and the second sum runs over the divisors of $M'$, both being natural numbers cast into $\mathbb{Q}$. Note that the arithmetic on the right-hand side is performed in $\mathbb{Q}$, so no integrality of the individual terms is claimed.
--
--   This is the classical genus formula $g = 1 + \mu/12 - \nu_2/4 - \nu_3/3 - \nu_\infty/2$ specialised to $\Gamma(q) \cap \Gamma_0(M')$ (conjugated to a $\Gamma_H$ of level $q^2M'$), where for $q \ge 5$ there are no elliptic points, the index contributes $q(q^2-1)\psi(M')$ and the cusps contribute $(q^2-1)$ times the cusp count $\sum_{d \mid M'}\varphi(\gcd(d,M'/d))$ of $X_0(M')$. It feeds the comparison of this genus with the Igusa supersingular chart count in [`ModularCurve.FullLevel.genusFF_fieldBar_add_eq_of_igusa_supersingular_charts`](thm.html#ModularCurve.FullLevel.genusFF_fieldBar_add_eq_of_igusa_supersingular_charts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_genusFF_fieldBar_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve.FullLevel
open AlgebraicCurve
open ModularCurve

theorem ModularCurve.FullLevel.genusFF_fieldBar_eq
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') :
    (AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(fieldBar q M') : ℚ) =
      1 + (q : ℚ) * ((q : ℚ) ^ 2 - 1) * dedekindPsi M' / 24 -
        ((q : ℚ) ^ 2 - 1) * ((∑ d ∈ M'.divisors, Nat.totient (Nat.gcd d (M' / d)) : ℕ) : ℚ) / 4 := by sorry
