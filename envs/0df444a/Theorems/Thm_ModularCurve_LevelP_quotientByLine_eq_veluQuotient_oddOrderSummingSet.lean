-- Prove2me | Theorems.Thm_ModularCurve_LevelP_quotientByLine_eq_veluQuotient_oddOrderSummingSet
-- name    : ModularCurve.LevelP.quotientByLine_eq_veluQuotient_oddOrderSummingSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/da3569ed-f334-5da7-8207-4ffc006c7339
-- title:
--   Vélu's x-only quotient equals the summing-set quotient
-- statement:
--   Let $F$ be a field with decidable equality, $W$ a Weierstrass curve over $F$ which is elliptic, $p$ a natural number with $p$ odd, and let $(x,y)$ be a point satisfying the affine nonsingularity condition `W.toAffine.Nonsingular x y`, so that $Q :=$ `WeierstrassCurve.Affine.Point.some x y h` is a point of the affine group $W(F)$; assume $Q$ has additive order exactly $p$. The assertion is an equality of Weierstrass curves over $F$: on the one side, [`ModularCurve.LevelP.quotientByLine W p x`](def/ModularCurve_KatzLevelPQuotient.html#L45), the curve with the same $a_1,a_2,a_3$ as $W$ and with $a_4 = W.a_4 - 5t$, $a_6 = W.a_6 - b_2 t - 7w$, where $t = \sum_{k=1}^{(p-1)/2}(6x_k^2 + b_2 x_k + b_4)$ and $w = \sum_{k=1}^{(p-1)/2}(\Psi_2^2(x_k) + x_k(6x_k^2 + b_2x_k + b_4))$ with $x_k =$ [`ModularCurve.LevelP.smulX W k x`](def/ModularCurve_KatzLevelPQuotient.html#L16), the $x$-only multiplication expression which over a field equals $\Phi_k(x)/\Psi_k^2(x)$; on the other side, `W.veluQuotient S`, built from the same $a_1,a_2,a_3$ and from $a_4 = W.a_4 - 5\,\mathrm{veluTSum}(S)$, $a_6 = W.a_6 - b_2\,\mathrm{veluTSum}(S) - 7\,\mathrm{veluWSum}(S)$, the sums of Vélu's local quantities `veluT` and `veluW` over the finite set $S =$ `W.oddOrderSummingSet Q ((p-1)/2)` of coordinate pairs of the points $k\cdot Q$ for $1 \le k \le (p-1)/2$.
--
--   This identifies the $y$-free, division-polynomial presentation of Vélu's isogeny formulas used in the level-$p$ moduli dictionary with the point-set presentation of Vélu's quotient taken over the multiples $Q, 2Q, \dots, \frac{p-1}{2}Q$ of a point of exact order $p$. It is used in the treatment of the level-$p$ structure, notably to transfer invertibility of the discriminant of the quotient curve and to compare quotients by points lying on the same line.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelP_quotientByLine_eq_veluQuotient_oddOrderSummingSet.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPQuotient
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.LevelP.quotientByLine_eq_veluQuotient_oddOrderSummingSet
    {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic] {p : ℕ}
    (hp : Odd p) {x y : F} (h : W.toAffine.Nonsingular x y)
    (hQ : addOrderOf (WeierstrassCurve.Affine.Point.some x y h) = p) :
    ModularCurve.LevelP.quotientByLine W p x =
      W.veluQuotient (W.oddOrderSummingSet (WeierstrassCurve.Affine.Point.some x y h) ((p - 1) / 2)) := by sorry
