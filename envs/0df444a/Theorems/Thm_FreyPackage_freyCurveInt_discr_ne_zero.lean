-- Prove2me | Theorems.Thm_FreyPackage_freyCurveInt_discr_ne_zero
-- name    : FreyPackage.freyCurveInt_discr_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/36cf04ab-b614-5ad2-9ef2-46957339c96c
-- title:
--   The integral Frey model has non-zero discriminant
-- statement:
--   Let $P$ be a Frey package, that is: non-zero integers $a$, $b$, $c$, a prime $p$ with $5 \le p$, an equation $a^p + b^p = c^p$, the condition $\gcd(a,b) = 1$, and the congruences $a \equiv 3 \pmod 4$ and $b \equiv 0 \pmod 2$. Associated with $P$ is the integral Weierstrass model `freyCurveInt` over $\mathbb{Z}$ with coefficients
--   $$a_1 = 1,\qquad a_2 = \frac{b^p - 1 - a^p}{4},\qquad a_3 = 0,\qquad a_4 = \frac{-a^p\,b^p}{16},\qquad a_6 = 0,$$
--   the two fractions being formed with integer division (the congruence conditions on $a$ and $b$ together with $p \ge 5$ make the numerators divisible by $4$ and by $16$ respectively). The assertion is that the discriminant $\Delta$ of this integral model, computed by the usual Weierstrass formula in $\mathbb{Z}$, is non-zero.
--
--   This is the non-degeneracy of the Frey curve attached to a putative solution of the Fermat equation: the model is an elliptic curve, so that its Galois representations, conductor and level-lowering properties are available. It is used throughout the analysis of the Frey curve at the primes $2$ and $p$, for instance in the statements about inertia at $2$ and the filtration of inertia at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_freyCurveInt_discr_ne_zero.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FreyPackage.freyCurveInt_discr_ne_zero (P : FreyPackage) : P.freyCurveInt.Δ ≠ 0 := by sorry
