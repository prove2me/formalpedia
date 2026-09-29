-- Prove2me | Theorems.Thm_ModularCurve_eval_prePsi_tateBase_cuspPoint_eq_zero_of_five_le
-- name    : ModularCurve.eval_prePsi_tateBase_cuspPoint_eq_zero_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/3d48e30f-e909-59c5-ae79-5204a2c31060
-- title:
--   Cusp points of the Tate curve are p-torsion, p ≥ 5
-- statement:
--   Let $R$ be a commutative ring and $p$ a prime with $5 \le p$, and assume that the image of $p$ in $R$ is a unit. Let $\zeta \in R^{\times}$ satisfy $\sum_{i<p} \zeta^{i} = 0$, and let $v : \mathrm{Fin}\,2 \to \mathbb{Z}/p$ be a non-zero pair of residues. Consider the Weierstrass curve [`ModularCurve.tateBase R p`](def/ModularCurve_TateSlots.html#L46) over the Laurent series ring $R((q))$: it is the universal Tate curve `tatePowerSeries`, with its coefficients pushed into Laurent series over $R$, transported along the ring homomorphism [`ModularCurve.qExpand`](def/ModularCurve_X0.html#L25) that multiplies all Hahn-series exponents by $p$ (i.e. the substitution $q \mapsto q^{p}$). Write $a = (v\,0).\mathrm{val}$ and $b = (v\,1).\mathrm{val}$ for the canonical representatives in $\{0,\dots,p-1\}$. The point [`ModularCurve.cuspPoint R p ζ v`](def/ModularCurve_KatzLevelPCusps.html#L59) is defined by cases: if $v\,1 = 0$ it is the toric point [`ModularCurve.tateToricPoint R p (ζ ^ a)`](def/ModularCurve_KatzLevelPCusps.html#L20), whose two coordinates are the explicit power series in $q$ attached to the parameter $\zeta^{a}$, and otherwise it is [`ModularCurve.nonToricPoint R p (ζ ^ a) b`](def/ModularCurve_TateSlots.html#L35), whose coordinates come from the substitution `slotSubst` applied to the universal series `tateUnivX` and `tateUnivY`. The assertion is that the Mathlib polynomial $\mathrm{pre}\Psi_{p}$ of [`ModularCurve.tateBase R p`](def/ModularCurve_TateSlots.html#L46), evaluated at the first (abscissa) coordinate of this point, is $0$.
--
--   In classical terms: on the Tate curve $\mathbb{G}_m/q^{p\mathbb{Z}}$ over $R((q))$ the parameter $\zeta^{a}q^{b}$ defines a $p$-torsion point for every $(a,b) \neq (0,0)$ in $(\mathbb{Z}/p)^{2}$, expressed through the vanishing of the $p$-division polynomial at its $x$-coordinate. It is the common generalisation of the toric and non-toric cases, and is used in the construction of the level-$p$ structure on the cusp data, [`ModularCurve.isLevelPStructure_cuspData`](thm.html#ModularCurve.isLevelPStructure_cuspData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eval_prePsi_tateBase_cuspPoint_eq_zero_of_five_le.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.eval_prePsi_tateBase_cuspPoint_eq_zero_of_five_le {R : Type u} [CommRing R] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (hp : IsUnit (p : R)) (ζ : Rˣ)
    (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) (v : Fin 2 → ZMod p) (hv : v ≠ 0) :
    ((ModularCurve.tateBase R p).preΨ (p : ℤ)).eval (ModularCurve.cuspPoint R p ζ v).1 = 0 := by sorry
