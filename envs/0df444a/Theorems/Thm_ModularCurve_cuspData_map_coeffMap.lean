-- Prove2me | Theorems.Thm_ModularCurve_cuspData_map_coeffMap
-- name    : ModularCurve.cuspData_map_coeffMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/e4a65ce3-fe38-54da-b1e8-74e693e0917d
-- title:
--   Naturality of level-p cusp data under coefficient base change
-- statement:
--   Let $R$ and $S$ be commutative rings, $f\colon R\to S$ a ring homomorphism, and $p$ a prime number. Assume that the image of $p$ in $R$ is a unit, and let $\zeta\in R^\times$ be a unit satisfying $\sum_{i=0}^{p-1}\zeta^i=0$. Let $v,w\colon \mathrm{Fin}\,2\to\mathbb Z/p$ be two pairs of indices. The level-$p$ data [`ModularCurve.cuspData R p ζ v w`](def/ModularCurve_KatzLevelPCusps.html#L71) is the `LevelPData` record over the Laurent series ring `LaurentSeries R` whose coordinates $(x_P,y_P)$ are the two components of [`ModularCurve.cuspPoint R p ζ v`](def/ModularCurve_KatzLevelPCusps.html#L59) and whose coordinates $(x_Q,y_Q)$ are those of [`ModularCurve.cuspPoint R p ζ w`](def/ModularCurve_KatzLevelPCusps.html#L59), where `cuspPoint R p ζ v` is `tateToricPoint R p (ζ ^ (v 0).val)` when $v_1=0$ and `nonToricPoint R p (ζ ^ (v 0).val) (v 1).val` otherwise. The assertion is that transporting this record along the ring homomorphism [`ModularCurve.coeffMap f`](def/ModularCurve_LaurentCoeff.html#L16), which sends a Laurent series over $R$ to the Laurent series over $S$ obtained by applying $f$ to each coefficient, i.e. applying `coeffMap f` to each of the four coordinates, yields exactly [`ModularCurve.cuspData S p (Units.map f ζ) v w`](def/ModularCurve_KatzLevelPCusps.html#L71), the level-$p$ data over `LaurentSeries S` formed with the same indices $v,w$ and with the unit $f(\zeta)$ of $S$.
--
--   This is the compatibility of the level-$p$ structure at the cusps of the Tate curve with change of coefficient ring, applied coefficientwise to the $q$-expansions of the four affine coordinates; it underlies the passage between coefficient rings in the $q$-expansion principle for Katz modular forms. It is used in the vanishing criteria for Katz level-$p$ forms whose values at the cusps vanish over all fields, and in the construction of a Katz $\Gamma_0$-form with prescribed values at the cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_cuspData_map_coeffMap.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.cuspData_map_coeffMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (p : R)) (ζ : Rˣ)
    (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) (v w : Fin 2 → ZMod p) :
    (ModularCurve.cuspData R p ζ v w).map (ModularCurve.coeffMap f) =
      ModularCurve.cuspData S p (Units.map (f : R →* S) ζ) v w := by sorry
