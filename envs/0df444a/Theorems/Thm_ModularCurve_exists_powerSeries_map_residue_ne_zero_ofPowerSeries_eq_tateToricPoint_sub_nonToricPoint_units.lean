-- Prove2me | Theorems.Thm_ModularCurve_exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_nonToricPoint_units
-- name    : ModularCurve.exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_nonToricPoint_units
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/73f5a7a7-9f74-5cb1-bec1-ded950fc9784
-- title:
--   An integral q-series with non-zero reduction: toric minus non-toric abscissa
-- statement:
--   Let $L$ be a field of characteristic zero and let $A$ be a discrete valuation domain equipped with an $A$-algebra structure on $L$ making $L$ the fraction field of $A$. Let $N$ be a non-zero natural number, let $c$ be a unit of $A$ such that $1-(c:A)$ is a unit of $A$, let $c'$ be a unit of $A$, and let $j$ be a natural number with $0<j<N$. The assertion is that there is a power series $P$ over $A$ with two properties: first, the image of $P$ under coefficientwise reduction along the residue map $A \to A/\mathfrak{m}_A$ is non-zero; second, the Hahn series over $\mathbb{Z}$ obtained from the image of $P$ along $A \to L$ equals the difference of the first components of [`ModularCurve.tateToricPoint L N`](def/ModularCurve_KatzLevelPCusps.html#L20) at the image of $c$ in $L^{\times}$ and of [`ModularCurve.nonToricPoint L N`](def/ModularCurve_TateSlots.html#L35) at the image of $c'$ in $L^{\times}$ and the index $j$. Here the first component of the toric point is the power series whose constant coefficient is $(c)\cdot\mathrm{inverse}(1-c)^2$ and whose $m$-th coefficient for $m>0$ is $\sum_{d \mid m,\ N \mid d} (m/d)\bigl(c^{m/d}+c^{-m/d}\bigr) - 2\,[N \mid m]\,\sigma_1(m/N)$, while the first component of the non-toric point is the power series $\mathrm{slotSubst}$ obtained by substituting $X_0 \mapsto c'X^{j}$, $X_1 \mapsto c'^{-1}X^{N-j}$ into the universal two-variable Tate abscissa series `tateUnivX`.
--
--   This compares the $x$-coordinates, as $q$-expansions, of the toric point $u=c$ and the non-toric point $u=c'q^{j}$ on the Tate curve $E_{q^{N}}$, and records that their difference is integral over the discrete valuation ring $A$ with non-zero reduction modulo the maximal ideal. It is used in the construction of level automorphisms with prescribed integrality behaviour at a cusp, in the modular-curve input to the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_nonToricPoint_units.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_powerSeries_map_residue_ne_zero_ofPowerSeries_eq_tateToricPoint_sub_nonToricPoint_units
    (L : Type) [Field L] [CharZero L] (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A L] [IsFractionRing A L]
    (N : ℕ) [NeZero N] (c : Aˣ) (hc : IsUnit (1 - (c : A))) (c' : Aˣ) (j : ℕ) (hj : 0 < j) (hjN : j < N) :
    ∃ P : PowerSeries A, P.map (IsLocalRing.residue A) ≠ 0 ∧
      HahnSeries.ofPowerSeries ℤ L (P.map (algebraMap A L)) =
        (ModularCurve.tateToricPoint L N (Units.map (↑(algebraMap A L) : A →* L) c)).1 -
          (ModularCurve.nonToricPoint L N (Units.map (↑(algebraMap A L) : A →* L) c') j).1 := by sorry
