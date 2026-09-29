-- Prove2me | Theorems.Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_mazurCusp
-- name    : ModularCurve.isLevelPStructure_tateBase_cuspData_mazurCusp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/0313bf6b-b927-58d3-a906-2c59896153f3
-- title:
--   Mazur's cusp is a level-p structure on Tate(qᵖ)
-- statement:
--   Let $R$ be a commutative ring and $p$ a prime with $p \neq 2$ and $p$ invertible in $R$. Let $\zeta \in R^{\times}$ satisfy $\sum_{i=0}^{p-1}\zeta^{i} = 0$, and let $a \in \mathbb{Z}/p$ with $a \neq 0$. Write $W =$ [`ModularCurve.tateBase R p`](def/ModularCurve_TateSlots.html#L46), the Weierstrass curve over the Laurent series ring $R((q))$ obtained from the Tate curve `tateLaurent R` by applying the ring homomorphism `qExpand R p` that multiplies exponents by $p$ (that is, the Tate curve in the parameter $q^{p}$). The datum [`ModularCurve.cuspData R p ζ ![a, 0] ![0, 1]`](def/ModularCurve_KatzLevelPCusps.html#L71) consists of the two points $P$ and $Q$ of `cuspPoint`: since the second coordinate of $![a,0]$ vanishes, $P =$ `tateToricPoint R p (ζ ^ a.val)`, and since the second coordinate of $![0,1]$ is $1 \neq 0$, $Q =$ `nonToricPoint R p 1 1`. The assertion is that this pair satisfies `IsLevelPStructure W p`, i.e. all six conditions: the affine coordinates of $P$ and of $Q$ satisfy the Weierstrass equation of $W$; the polynomial $W.\mathrm{pre}\Psi(p)$ (indexed by the integer $p$) vanishes at $x_P$ and at $x_Q$; and both products $\prod_{b=1}^{(p-1)/2}\bigl(x_Q\,(W.\Psi\mathrm{Sq}\,b)(x_P) - (W.\Phi\,b)(x_P)\bigr)$ and $\prod_{b=1}^{(p-1)/2}\bigl(x_P\,(W.\Psi\mathrm{Sq}\,b)(x_Q) - (W.\Phi\,b)(x_Q)\bigr)$ are units in $R((q))$.
--
--   This is the statement that Mazur's cusp $(\mathrm{Tate}(q^{p}), \zeta^{a}, q)$ is an honest test object for the full level-$p$ moduli problem, in the division-polynomial formulation of a level-$p$ structure used here. It is invoked by the statements [`ModularCurve.isLevelPStructure_tateBase_cuspData_of_dvd`](thm.html#ModularCurve.isLevelPStructure_tateBase_cuspData_of_dvd) and [`ModularCurve.isLevelPStructure_tateBase_cuspData_neg_of_dvd`](thm.html#ModularCurve.isLevelPStructure_tateBase_cuspData_neg_of_dvd), which feed the $q$-expansion computations at the cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_mazurCusp.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.isLevelPStructure_tateBase_cuspData_mazurCusp
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : IsUnit (p : R))
    (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) (a : ZMod p) (ha : a ≠ 0) :
    ModularCurve.IsLevelPStructure (ModularCurve.tateBase R p) p
      (ModularCurve.cuspData R p ζ ![a, 0] ![0, 1]) := by sorry
