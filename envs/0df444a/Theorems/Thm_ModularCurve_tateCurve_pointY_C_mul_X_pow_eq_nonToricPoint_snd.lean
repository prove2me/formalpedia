-- Prove2me | Theorems.Thm_ModularCurve_tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd
-- name    : ModularCurve.tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/bb4611d9-328a-508d-b5e3-04b76d641d88
-- title:
--   Tate ordinate at u = c t^j equals the non-toric slot point
-- statement:
--   Let $F$ be a field, $p$ a natural number, $c$ a unit of $F$, and $j$ a natural number with $0 < j$ and $j < p$. Write $t$ for `HahnSeries.single (1 : ℤ) (1 : F)`, the uniformiser of the Laurent series field `LaurentSeries F`, taken with its $t$-adic norm, for which it is a complete ultrametric nontrivially normed field. The assertion is an equality of two elements of `LaurentSeries F`. On the left is [`TateCurve.pointY`](def/TateCurve_PointSeries.html#L181) evaluated at $q = t^{p}$ and $u = \mathrm{C}(c)\,t^{j}$, that is, the sum over $n \in \mathbb{Z}$ (as an unconditional sum in the $t$-adic topology) of `yfun` applied to $q^{n}u$, plus the term `s₁ q`. On the right is the second coordinate of [`ModularCurve.nonToricPoint F p c j`](def/ModularCurve_TateSlots.html#L35), namely the Laurent series obtained via `HahnSeries.ofPowerSeries` from the one-variable power series `slotSubst F p c j tateUnivY`, the substitution of the family `slotFamily F p c j` into the two-variable integral series `tateUnivY` over $\mathbb{Z}$, whose coefficient at an exponent $(e_0,e_1)$ equals $\sum_{d \mid e_1} d$ if $e_0 = e_1$; equals $\binom{e_0-e_1}{2}$ if $e_1 < e_0$ and $e_0-e_1 \mid e_1$, and $0$ if $e_1<e_0$ without that divisibility; and equals $-\binom{e_1-e_0+1}{2}$ if $e_0 < e_1$ and $e_1-e_0 \mid e_1$, and $0$ otherwise.
--
--   This is the ordinate half of the identification of the Tate parametrisation, evaluated at the non-toric slot $u = c\,t^{j}$ of the Tate curve with parameter $q = t^{p}$ over $F((t))$, with the closed-form power series in $t$ produced by substituting into the universal two-variable Tate series; the abscissa is treated by the companion statement for `tateUnivX`. It is used by [`ModularCurve.toricPoint_add_nonToricPoint_of_charZero`](thm.html#ModularCurve.toricPoint_add_nonToricPoint_of_charZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd.lean

import Mathlib
import Definitions.Def_LaurentSeries_XAdic
import Definitions.Def_TateCurve_PointSeries
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped LaurentSeries.XAdic

theorem ModularCurve.tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd (F : Type*) [Field F] (p : ℕ) [NeZero p]
    (c : Fˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    TateCurve.pointY ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
        (HahnSeries.C (c : F) * (HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ j)
      = (ModularCurve.nonToricPoint F p c j).2 := by sorry
