-- Prove2me | Theorems.Thm_FreyCurve_eight_mul_Psi2Sq_eval_reductionMod
-- name    : FreyCurve.eight_mul_Psi2Sq_eval_reductionMod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/892f0ebf-fc12-5f56-b500-579e43787d5f
-- title:
--   Factorisation of 8Ψ₂² for the reduced Frey curve
-- statement:
--   Let $P$ be a Frey package, that is, nonzero integers $a,b,c$ together with a prime $p\ge 5$ such that $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$; let $q$ be a prime and $x\in\mathbb{Z}/q$. Here [`FreyPackage.freyCurveInt P`](def/FLTPrelim_FreyPackage.html#L83) is the Weierstrass curve over $\mathbb{Z}$ with coefficients $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$ (integer division, legitimate under the congruence conditions of a Frey package), and `reductionMod q` is the Weierstrass curve over $\mathbb{Z}/q$ obtained by applying the ring homomorphism $\mathbb{Z}\to\mathbb{Z}/q$ to these coefficients. The assertion is the identity, in $\mathbb{Z}/q$,
--   $$8\cdot\Psi_2^2(x)=2x\,(4x-\bar a^{\,p})(4x+\bar b^{\,p}),$$
--   where $\Psi_2^2=4X^3+b_2X^2+2b_4X+b_6$ is the square of the $2$-division polynomial of the reduced curve, evaluated at $x$, and $\bar a,\bar b$ denote the images of $a,b$ in $\mathbb{Z}/q$. The factor $8$ on the left makes the statement an identity in $\mathbb{Z}/q$ for every $q$, including $q=2$.
--
--   This exhibits the $2$-division polynomial of the reduced Frey curve as a product of linear factors with roots $0$, $\bar a^{\,p}/4$, $-\bar b^{\,p}/4$ once $8$ is invertible, the reduction of the rational factorisation coming from the model $y^2=x(x-a^p)(x+b^p)$. It is used in the count of $2$-torsion points of the reduction, [`FreyCurve.card_two_torsion_reductionMod`](thm.html#FreyCurve.card_two_torsion_reductionMod), en route to the reduction-type analysis of the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyCurve_eight_mul_Psi2Sq_eval_reductionMod.lean

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_FreyPackage
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace FreyCurve
open WeierstrassCurve

theorem eight_mul_Psi2Sq_eval_reductionMod (P : FreyPackage) {q : ℕ} [Fact q.Prime]
    (x : ZMod q) :
    8 * (((FreyPackage.freyCurveInt P).reductionMod q).Ψ₂Sq.eval x) =
      2 * x * (4 * x - ((P.a : ZMod q)) ^ P.p) * (4 * x + ((P.b : ZMod q)) ^ P.p) := by sorry
