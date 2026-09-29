-- Prove2me | Theorems.Thm_ModularCurve_equation_tateBase_cuspPoint
-- name    : ModularCurve.equation_tateBase_cuspPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/a06d8132-156e-5b6a-b7ed-73ef7f8c1cf5
-- title:
--   Cusp points lie on the Tate curve over R((q))
-- statement:
--   Let $R$ be a commutative ring and $p$ a prime such that the image of $p$ in $R$ is a unit, let $\zeta \in R^{\times}$ satisfy $\sum_{i<p} \zeta^{i} = 0$, and let $v : \mathrm{Fin}\,2 \to \mathbb{Z}/p$ be a nonzero pair $v = (v_0, v_1)$. The assertion is that the pair of Laurent series [`ModularCurve.cuspPoint R p ζ v`](def/ModularCurve_KatzLevelPCusps.html#L59) satisfies the affine Weierstrass equation of the curve [`ModularCurve.tateBase R p`](def/ModularCurve_TateSlots.html#L46) over `LaurentSeries R`, i.e. of the Tate curve `tateLaurent R` (the universal Tate Weierstrass curve `tatePowerSeries`, pushed into Laurent series) with its coefficients transported by the ring homomorphism `qExpand R p`, which multiplies all Hahn-series exponents by $p$ — the curve $\mathrm{Tate}(q^{p})$. Here `cuspPoint R p ζ v` is, by definition, the toric point `tateToricPoint R p (ζ ^ (v 0).val)`, whose two coordinates are the explicit power series in $q$ built from divisor sums in $c = \zeta^{v_0}$ and $c^{-1}$, in case $v_1 = 0$; and otherwise the point `nonToricPoint R p (ζ ^ (v 0).val) (v 1).val`, whose coordinates are obtained by applying `slotSubst` with parameters $c = \zeta^{v_0}$ and $j = (v_1).\mathrm{val}$ to the universal coordinates `tateUnivX`, `tateUnivY`.
--
--   This records that each of the $p^{2}-1$ nontrivial points $u = \zeta^{a} q^{b}$ of the Tate parametrisation, as formalised by [`ModularCurve.cuspPoint`](def/ModularCurve_KatzLevelPCusps.html#L59), is an honest point of $\mathrm{Tate}(q^{p})$ over $R((q))$. It is one of the inputs to [`ModularCurve.isLevelPStructure_cuspData`](thm.html#ModularCurve.isLevelPStructure_cuspData), which shows that a pair of such points with nonvanishing determinant gives a level-$p$ structure on the Tate curve at a cusp.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_equation_tateBase_cuspPoint.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.equation_tateBase_cuspPoint {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    (hp : IsUnit (p : R)) (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0)
    (v : Fin 2 → ZMod p) (hv : v ≠ 0) :
    (ModularCurve.tateBase R p).toAffine.Equation
      (ModularCurve.cuspPoint R p ζ v).1 (ModularCurve.cuspPoint R p ζ v).2 := by sorry
