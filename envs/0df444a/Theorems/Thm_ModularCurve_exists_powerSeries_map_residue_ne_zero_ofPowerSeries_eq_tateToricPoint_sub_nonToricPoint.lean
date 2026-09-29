-- Prove2me | Theorems.Thm_ModularCurve_exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_nonToricPoint
-- name    : ModularCurve.exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_nonToricPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/9ef1c382-49fb-5205-88e2-3cf562ae78b5
-- title:
--   Toric minus non-toric Tate abscissa: integral, nonzero reduction
-- statement:
--   Let $L$ be a field of characteristic zero and $A$ a discrete valuation domain with $\mathrm{Algebra}\,A\,L$ realising $L$ as the fraction field of $A$; let $N$ be a non-zero natural number, $c \in A^{\times}$ a unit such that $1 - c$ is also a unit of $A$, and $j$ a natural number with $0 < j < N$. The assertion is that there exists a power series $P \in A[[q]]$ with two properties. First, the image of $P$ under the coefficientwise residue map $A \to A/\mathfrak m$ is non-zero. Second, the Laurent (Hahn) series over $L$ obtained from the coefficientwise image of $P$ in $L[[q]]$ equals the difference of the first components of two pairs of Laurent series: from [`ModularCurve.tateToricPoint L N c'`](def/ModularCurve_KatzLevelPCusps.html#L20), where $c'$ is the image of $c$ in $L^{\times}$, namely the series whose $0$-th coefficient is $c'\cdot(1-c')^{-2}$ (via `Ring.inverse`) and whose $m$-th coefficient for $m > 0$ is $\sum_{d \mid m,\ N \mid d} (m/d)\bigl(c'^{\,m/d} + c'^{-m/d}\bigr) - 2\bigl[N \mid m\bigr]\sum_{e \mid m/N} e$; minus, from [`ModularCurve.nonToricPoint L N 1 j`](def/ModularCurve_TateSlots.html#L35), the series `slotSubst L N 1 j tateUnivX`, i.e. the substitution of the two-variable integral series `tateUnivX`, whose coefficient at an exponent $e$ is $-2\sum_{d \mid e_1} d$ when $e_0 = e_1$, is $e_0-e_1$ or $0$ according as $e_0-e_1$ divides $e_1$ when $e_1 < e_0$, and symmetrically when $e_0 < e_1$, along the slot family attached to $N$, the unit $1$ and $j$.
--
--   This is the statement that the difference between the $x$-coordinate of a toric point $u = c$ and that of the non-toric point $u = q^{j}$ on the Tate curve $\mathrm{Tate}(q^{N})$ is given by an integral $q$-expansion whose reduction modulo the maximal ideal of $A$ does not vanish, so that this difference is a "Gauss unit" usable as a denominator after reduction. It is used in the construction of auxiliary level structures and charts, through [`ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_mem_chartAlgFin_coe_eq_slotSubst_sub_and_apply_eq_laurent`](thm.html#ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_mem_chartAlgFin_coe_eq_slotSubst_sub_and_apply_eq_laurent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_nonToricPoint.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_nonToricPoint
    (L : Type) [Field L] [CharZero L] (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A L] [IsFractionRing A L]
    (N : ℕ) [NeZero N] (c : Aˣ) (hc : IsUnit (1 - (c : A))) (j : ℕ) (hj : 0 < j) (hjN : j < N) :
    ∃ P : PowerSeries A, P.map (IsLocalRing.residue A) ≠ 0 ∧
      HahnSeries.ofPowerSeries ℤ L (P.map (algebraMap A L)) =
        (ModularCurve.tateToricPoint L N (Units.map (↑(algebraMap A L) : A →* L) c)).1 -
          (ModularCurve.nonToricPoint L N 1 j).1 := by sorry
