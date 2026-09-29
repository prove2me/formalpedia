-- Prove2me | Theorems.Thm_FreyPackage_not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve
-- name    : FreyPackage.not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/61b4a41c-7bb9-5989-a4d8-c682c675aff8
-- title:
--   Bad reduction at primes dividing abc for all integral models
-- statement:
--   Let $P$ be a Frey package: nonzero integers $a,b,c$, a prime $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$; its Frey curve $E=P.\mathtt{freyCurve}$ is the Weierstrass curve over $\mathbb{Q}$ with $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. Let $W$ be a Weierstrass curve with coefficients in $\mathbb{Z}$ which is an integral model of $E$ in the sense that some variable change $C$ over $\mathbb{Q}$ carries $E$ to the base change of $W$ along $\mathbb{Z}\to\mathbb{Q}$, i.e. $C\bullet E = W_{\mathbb{Q}}$. Let $\ell$ be a prime number dividing the product $abc$ in $\mathbb{Z}$. The conclusion is that $\ell$ is not a good prime for $W$, where being a good prime is defined as $\ell\nmid\Delta(W)$; thus the assertion is the (classically equivalent) double negation of $\ell \mid \Delta(W)$, the divisibility of the discriminant of $W$ by $\ell$.
--
--   The statement says that a prime of multiplicative reduction for the Frey curve is a prime of bad reduction for every integral Weierstrass model, minimal or not: the set of primes dividing the discriminant of an arbitrary integral model contains all primes dividing $abc$. It is used in the level-lowering part of the argument, where a good prime of an auxiliary integral model must be excluded from the primes supporting the conductor, and is cited by [`FreyPackage.freyCurveApOfModelThreeAgreement`](thm.html#FreyPackage.freyCurveApOfModelThreeAgreement) and [`FreyPackage.level_lowering_at_p_of_conductorLevel`](thm.html#FreyPackage.level_lowering_at_p_of_conductorLevel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve

theorem FreyPackage.not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve (P : FreyPackage) {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf P.freyCurve) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓabc : (ℓ : ℤ) ∣ P.a * P.b * P.c) : ¬ W.IsGoodPrimeFor ℓ := by sorry
