-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_genusFF_fieldBar_eq_of_eq_three
-- name    : ModularCurve.FullLevel.genusFF_fieldBar_eq_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/3482768d-51fd-513c-977a-c002d1d085b5
-- title:
--   Genus of the full level-3 modular function field
-- statement:
--   Let $q$ be a prime with $q = 3$, and let $M'$ be a positive integer not divisible by $q$. Let $H =$ `levelH q M'` be the kernel of the reduction map $(\mathbb{Z}/q^2M'\mathbb{Z})^\times \to (\mathbb{Z}/q\mathbb{Z})^\times$, and let $F =$ `fieldBar q M'` be the base change to $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` of the $X_H$ function field of level $q^2M'$ for this $H$, realised as an intermediate field of the Laurent series field $\overline{\mathbb{Q}}((q))$. The assertion is an identity in $\mathbb{Q}$ for the genus `genusFF` of $F$ over $\overline{\mathbb{Q}}$, that is, for the $\overline{\mathbb{Q}}$-dimension of $H^1$ of the zero divisor in $\mathrm{Place}(\overline{\mathbb{Q}}, F) \to_{f} \mathbb{Z}$, namely
--   $$\mathrm{genus}(F) = 1 + \frac{q(q^2-1)\,\psi(M')}{24} - \frac{(q^2-1)\,c_0(M')}{4},$$
--   where $\psi(M') =$ `dedekindPsi M'` is the sum of $M'/d$ over the squarefree divisors $d$ of $M'$, and $c_0(M') = \sum_{d \mid M'} \varphi(\gcd(d, M'/d))$. The right-hand side is written in terms of $q$, so that with $q = 3$ the stated value is $1 + \psi(M') - 2c_0(M')$.
--
--   This is the classical genus formula for the modular curve attached to $\Gamma_H(q^2M')$ — here $H$ the kernel of reduction to $(\mathbb{Z}/q\mathbb{Z})^\times$ — at the prime $q = 3$, giving the same closed expression in $q$, $\psi(M')$ and the cusp count $c_0(M')$ of $X_0(M')$ as for larger primes. It feeds the comparison of the genus of this curve with the contribution of the Igusa supersingular charts in the case $q = 3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_genusFF_fieldBar_eq_of_eq_three.lean

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

theorem ModularCurve.FullLevel.genusFF_fieldBar_eq_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') :
    (AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(fieldBar q M') : ℚ) =
      1 + (q : ℚ) * ((q : ℚ) ^ 2 - 1) * dedekindPsi M' / 24 -
        ((q : ℚ) ^ 2 - 1) * ((∑ d ∈ M'.divisors, Nat.totient (Nat.gcd d (M' / d)) : ℕ) : ℚ) / 4 := by sorry
