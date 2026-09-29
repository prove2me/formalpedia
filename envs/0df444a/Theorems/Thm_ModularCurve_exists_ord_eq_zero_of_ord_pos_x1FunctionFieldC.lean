-- Prove2me | Theorems.Thm_ModularCurve_exists_ord_eq_zero_of_ord_pos_x1FunctionFieldC
-- name    : ModularCurve.exists_ord_eq_zero_of_ord_pos_x1FunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/53034354-88d8-5aa8-a0d2-5b03334a3487
-- title:
--   Nonvanishing integral forms at places above j=0 and 1728
-- statement:
--   Let $p$ be a prime with $p\ge 5$, let $\kappa$ be an algebraically closed field of characteristic $p$, and let $M\ge 5$ be a natural number with $p\nmid M$. Write $K_0=$ [`ModularCurve.x1FunctionFieldC κ M`](def/ModularCurve_X1.html#L134) for the intermediate field of the Laurent series field `LaurentSeries κ` obtained by adjoining to $\kappa$ the set `intFormRatiosC κ (Gamma1 M)`, the $q$-expansion model of the function field of $X_1(M)$ over $\kappa$. Let $J\in K_0$ be an element whose underlying Laurent series is [`ModularCurve.jqModC κ`](def/ModularCurve_JqCoeff.html#L15), namely $q^{-1}$ times the reduction to $\kappa$ of the integral power series `jNum` $=E_4^3\cdot$ `dedekindEtaUnitInv`, and let $x$ be a place of $K_0$ over $\kappa$: a valuation subring of $K_0$ containing $\kappa$, distinct from $K_0$ itself and a principal ideal ring, with $x.\mathrm{ord}$ the associated normalised additive valuation. Two implications are asserted. First, if $\mathrm{ord}_x J>0$, then there are a natural number $k$ with $3\nmid k$, a modular form $g$ of weight $k$ on $\Gamma_1(M)$, a power series $pg$ over $\mathbb{Z}$ whose image in $\mathbb{C}[[q]]$ is the $q$-expansion of $g$ of width $1$, with reduction `intSeriesC κ pg` $\ne 0$, and an element $t\in K_0$ whose Laurent series is $$\bigl(\text{reduction of }(X\cdot\mathrm{dedekindEtaUnit})^k\bigr)\big/\bigl(\text{reduction of }pg^{12}\bigr),$$ i.e. $\bar\Delta^k/\bar g^{12}$, such that $\mathrm{ord}_x t=0$. Second, the same conclusion holds with $3\nmid k$ replaced by $2\nmid k$ under the hypothesis $\mathrm{ord}_x\bigl(J-1728\bigr)>0$, where $1728$ is taken in $\kappa$ and mapped into $K_0$.
--
--   This is the statement that the integral $\Gamma_1(M)$-forms of weight prime to $3$ (respectively of odd weight) have no common zero at a place of $X_1(M)_\kappa$ lying over $j=0$ (respectively $j=1728$), expressed in the trivialisation in which a weight-$k$ form is measured by $\bar\Delta^k/\bar g^{12}$. It is used in the computation of $\mathrm{ord}_x(J-\lambda)$ at places of the $q$-expansion function field, namely in [`ModularCurve.ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC`](thm.html#ModularCurve.ord_sub_algebraMap_eq_jWidth_of_place_x1FunctionFieldC).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ord_eq_zero_of_ord_pos_x1FunctionFieldC.lean

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

theorem ModularCurve.exists_ord_eq_zero_of_ord_pos_x1FunctionFieldC
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (J : ↥(ModularCurve.x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = ModularCurve.jqModC κ)
    (x : Place κ ↥(ModularCurve.x1FunctionFieldC κ M)) :
    (0 < x.ord J →
      ∃ (k : ℕ) (g : ModularForm (Gamma1 M) (k : ℤ)) (pg : PowerSeries ℤ) (t : ↥(ModularCurve.x1FunctionFieldC κ M)),
        ¬ 3 ∣ k ∧ IsIntegralQExp g pg ∧ intSeriesC κ pg ≠ 0 ∧
        (t : LaurentSeries κ) =
          intSeriesC κ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ k) / intSeriesC κ (pg ^ 12) ∧
        x.ord t = 0) ∧
    (0 < x.ord (J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) →
      ∃ (k : ℕ) (g : ModularForm (Gamma1 M) (k : ℤ)) (pg : PowerSeries ℤ) (t : ↥(ModularCurve.x1FunctionFieldC κ M)),
        ¬ 2 ∣ k ∧ IsIntegralQExp g pg ∧ intSeriesC κ pg ≠ 0 ∧
        (t : LaurentSeries κ) =
          intSeriesC κ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ k) / intSeriesC κ (pg ^ 12) ∧
        x.ord t = 0) := by sorry
