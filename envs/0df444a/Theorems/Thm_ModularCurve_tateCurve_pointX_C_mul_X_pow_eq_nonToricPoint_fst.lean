-- Prove2me | Theorems.Thm_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst
-- name    : ModularCurve.tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/32889849-8363-55b7-8bc8-ad76f4bb6b75
-- title:
--   Tate parametrisation at u=c t^j: closed form for X
-- statement:
--   Let $F$ be a field and $p$ a natural number, and give the Laurent series field $\mathrm{LaurentSeries}\,F = F((t))$ its $X$-adic (i.e. $t$-adic) norm, for which it is a complete ultrametric nontrivially normed field. Let $c \in F^{\times}$ and let $j$ be a natural number with $0 < j$ and $j < p$. Put $t =$ `HahnSeries.single 1 1`, so $q = t^{p}$ and $u = c\,t^{j}$, the latter being the constant Hahn series attached to $c$ times $t^{j}$. Then the value [`TateCurve.pointX`](def/TateCurve_PointSeries.html#L179) $q\,u$, that is the unconditional sum over $n \in \mathbb{Z}$ of `xfun` $(q^{n}u)$ minus $2\,$`s₁`$\,q$, coincides with the first coordinate of the non-toric slot point [`ModularCurve.nonToricPoint F p c j`](def/ModularCurve_TateSlots.html#L35): namely with the Laurent series `HahnSeries.ofPowerSeries` of the one-variable power series over $F$ obtained by substituting the family `slotFamily F p c j` into the universal two-variable integral series `tateUnivX`, whose coefficient at a multi-exponent $e$ is $-2\sum_{d \mid e_1} d$ when $e_0 = e_1$, and otherwise $|e_0 - e_1|$ if $|e_0 - e_1|$ divides $e_1$ and $0$ if not.
--
--   This is the $x$-coordinate half of the identification of the Tate parametrisation at the non-toric argument $u = c\,t^{j}$ with a closed-form power series in $t$, the classical $q$-expansion for $X(u,q)$ specialised to $q = t^{p}$ over $F((t))$. Together with its $y$-coordinate counterpart it feeds the verification that the non-toric point satisfies the Weierstrass equation of the Tate curve and the computation of the sum of the toric and non-toric points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean

import Mathlib
import Definitions.Def_LaurentSeries_XAdic
import Definitions.Def_TateCurve_PointSeries
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped LaurentSeries.XAdic

theorem ModularCurve.tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst (F : Type*) [Field F] (p : ℕ) [NeZero p]
    (c : Fˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    TateCurve.pointX ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
        (HahnSeries.C (c : F) * (HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ j)
      = (ModularCurve.nonToricPoint F p c j).1 := by sorry
