-- Prove2me | Theorems.Thm_ModularCurve_three_dvd_mul_ord_and_two_dvd_mul_ord_sub_of_ord_eq_zero_x1FunctionFieldC
-- name    : ModularCurve.three_dvd_mul_ord_and_two_dvd_mul_ord_sub_of_ord_eq_zero_x1FunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/a83b86ee-6414-563c-a5e3-870774a0c1fb
-- title:
--   Divisibility of kcdotordₓ J by 3 and of kcdotordₓ(J-1728) by 2
-- statement:
--   Let $\kappa$ be a field and $M$ a nonzero natural number, and let $K_0 =$ [`ModularCurve.x1FunctionFieldC κ M`](def/ModularCurve_X1.html#L134) be the subfield of the Laurent series field $\kappa((q))$ obtained by adjoining to $\kappa$ the ratios of integral $q$-expansions attached to $\Gamma_1(M)$. Let $J \in K_0$ be an element whose underlying Laurent series is [`ModularCurve.jqModC κ`](def/ModularCurve_JqCoeff.html#L15), that is $q^{-1}$ times the reduction to $\kappa$ of the integral power series `jNum` $= E_4^3 \cdot \Delta^{-1}$ (with $\Delta$ given by $q\,\eta$-unit $= q\prod_{n\ge 1}(1-q^n)^{24}$). Let $k$ be a natural number, $g$ a modular form of weight $(k : \mathbb{Z})$ on $\Gamma_1(M)$, and $p_g \in \mathbb{Z}[[q]]$ an integral power series whose image in $\mathbb{C}[[q]]$ is the $q$-expansion of $g$; assume the reduction of $p_g$ to $\kappa((q))$ is nonzero. Let $t \in K_0$ be an element whose Laurent series is the quotient of the reduction of $(q\cdot\text{(}\eta\text{-unit)})^k$ by the reduction of $p_g^{12}$. Finally let $x$ be a place of $K_0$ over $\kappa$ (a proper valuation subring of $K_0$ containing $\kappa$ whose ring is a principal ideal ring), with associated order function $\operatorname{ord}_x$ the negative logarithm of its adic valuation, and suppose $\operatorname{ord}_x t = 0$. Then $3 \mid k\cdot\operatorname{ord}_x J$ and $2 \mid k\cdot\operatorname{ord}_x\bigl(J - 1728\bigr)$, where $1728$ denotes the image of $1728 \in \kappa$ in $K_0$.
--
--   The statement packages the local consequences of the identities $j\Delta = E_4^3$ and $E_4^3 - 1728\Delta = E_6^2$ at a place of the function field of $X_1(M)_\kappa$ at which a $k$-th power of $\Delta$ is comparable to the twelfth power of the reduction of a weight-$k$ form. It supplies the divisibility constraints above the points $j = 0$ and $j = 1728$ used in [`ModularCurve.ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC`](thm.html#ModularCurve.ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC), in the determination of the ramification of $X_1(M)_\kappa$ over the $j$-line. The proof invokes the identification of the $q$-expansion of the discriminant modular form with the reduction of $q\prod_{n \ge 1}(1-q^n)^{24}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_three_dvd_mul_ord_and_two_dvd_mul_ord_sub_of_ord_eq_zero_x1FunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup ModularCurve AlgebraicCurve
open scoped MatrixGroups ModularForm

theorem ModularCurve.three_dvd_mul_ord_and_two_dvd_mul_ord_sub_of_ord_eq_zero_x1FunctionFieldC
    (κ : Type) [Field κ] (M : ℕ) [NeZero M]
    (J : ↥(ModularCurve.x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = ModularCurve.jqModC κ)
    (k : ℕ) (g : ModularForm (Gamma1 M) (k : ℤ)) (pg : PowerSeries ℤ) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC κ pg ≠ 0)
    (t : ↥(ModularCurve.x1FunctionFieldC κ M))
    (ht : (t : LaurentSeries κ) =
      intSeriesC κ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ k) / intSeriesC κ (pg ^ 12))
    (x : Place κ ↥(ModularCurve.x1FunctionFieldC κ M)) (htx : x.ord t = 0) :
    (3 : ℤ) ∣ (k : ℤ) * x.ord J ∧
      (2 : ℤ) ∣ (k : ℤ) * x.ord (J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) := by sorry
