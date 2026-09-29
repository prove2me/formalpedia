-- Prove2me | Theorems.Thm_ModularCurve_exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_tateToricPoint_sq
-- name    : ModularCurve.exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_tateToricPoint_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/b6469ec8-af7c-5695-bfd6-9724d895c42b
-- title:
--   Integrality of x_T(c)-x_T(c²) with unit constant term
-- statement:
--   Let $L$ be a field of characteristic zero and let $A$ be a discrete valuation domain together with an $A$-algebra structure on $L$ exhibiting $L$ as the fraction field of $A$. Let $N$ be a natural number and let $c$ be a unit of $A$ such that $1-c$, $1-c^2$, $c-c^2$ and $1-c^3$ are all units of $A$. Write $x_T(d)$ for the first component of [`ModularCurve.tateToricPoint L N d`](def/ModularCurve_KatzLevelPCusps.html#L20), that is, for the Laurent series over $L$ coming from the power series whose $m$-th coefficient is $d\,(1-d)^{-2}$ for $m=0$ (inverse taken in the sense of `Ring.inverse`) and, for $m>0$, is $\sum_{e\mid m,\ N\mid e}(m/e)\bigl(d^{m/e}+d^{-m/e}\bigr)-2\,[\,N\mid m\,]\sum_{e\mid m/N}e$. The assertion is that there exists a power series $P$ over $A$ whose coefficientwise image under the residue map of $A$ onto its residue field is non-zero, and such that the Laurent series over $L$ obtained from the coefficientwise image of $P$ along $A\to L$ equals $x_T(c)-x_T(c^2)$, the unit arguments being the images of $c$ and $c^2$ in $L^\times$.
--
--   This is the integrality statement for the $x$-coordinate normaliser attached to the Tate curve in its toric coordinates: the difference of the two $q$-expansions at the toric points with parameters $c$ and $c^2$ already has coefficients in the valuation ring and does not vanish modulo the maximal ideal. It is used in the construction of level structures on the Tate curve near a cusp, where such a difference serves as the invertible normalising factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_tateToricPoint_sq.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_tateToricPoint_sq
    (L : Type) [Field L] [CharZero L] (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A L] [IsFractionRing A L]
    (N : ℕ) (c : Aˣ) (hc : IsUnit (1 - (c : A))) (hc2 : IsUnit (1 - (c : A) ^ 2))
    (hcc : IsUnit ((c : A) - (c : A) ^ 2)) (hc3 : IsUnit (1 - (c : A) ^ 3)) :
    ∃ P : PowerSeries A, P.map (IsLocalRing.residue A) ≠ 0 ∧
      HahnSeries.ofPowerSeries ℤ L (P.map (algebraMap A L)) =
        (ModularCurve.tateToricPoint L N (Units.map (↑(algebraMap A L) : A →* L) c)).1 -
          (ModularCurve.tateToricPoint L N (Units.map (↑(algebraMap A L) : A →* L) (c ^ 2))).1 := by sorry
