-- Prove2me | Theorems.Thm_ModularCurve_eval_prePsi_tateBase_tateToricPoint_eq_zero
-- name    : ModularCurve.eval_prePsi_tateBase_tateToricPoint_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/b09731d7-07b8-5542-b066-be84067af160
-- title:
--   Toric p-torsion points on Tate(qᵖ) kill ψₚ
-- statement:
--   Let $K$ be a commutative ring, $p$ a prime with $p \neq 2$, and let $c \in K^{\times}$ satisfy $c^{p} = 1$ and such that $1 - c$ is a unit of $K$. Consider the Weierstrass curve [`ModularCurve.tateBase K p`](def/ModularCurve_TateSlots.html#L46) over the field of Laurent series $K((q))$ (Hahn series over $\mathbb{Z}$ with coefficients in $K$): it is obtained from the integral Tate Weierstrass curve `tatePowerSeries`, pushed forward to $K((q))$, by the ring homomorphism `qExpand` that multiplies all exponents by $p$, i.e. it is $\mathrm{Tate}(q^{p})$. Let $x(c) \in K((q))$ be the first coordinate of [`ModularCurve.tateToricPoint K p c`](def/ModularCurve_KatzLevelPCusps.html#L20), the Laurent series whose constant Taylor coefficient is $c\,(1-c)^{-2}$ and whose $m$-th coefficient for $m \geq 1$ is $\sum_{d \mid m,\ p \mid d} (m/d)\bigl(c^{m/d} + c^{-m/d}\bigr) - 2\,[\,p \mid m\,]\sum_{e \mid m/p} e$. The assertion is that the division polynomial $\mathrm{pre}\Psi_{p}$ of $\mathrm{Tate}(q^{p})$, a polynomial in one variable over $K((q))$, vanishes at $x(c)$.
--
--   This is the statement that the toric points $u = c$ with $c^{p} = 1$, which lie in $\mu_{p} \subset \mathbb{G}_m/q^{p\mathbb{Z}}$, are $p$-torsion on the Tate curve $\mathrm{Tate}(q^{p})$, expressed through the vanishing of the $p$-division polynomial at their abscissa. It is used in the construction of the level-$p$ structure on $\mathrm{Tate}(q^{p})$ at the Mazur cusp, in [`ModularCurve.isLevelPStructure_tateBase_cuspData_mazurCusp`](thm.html#ModularCurve.isLevelPStructure_tateBase_cuspData_mazurCusp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eval_prePsi_tateBase_tateToricPoint_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.eval_prePsi_tateBase_tateToricPoint_eq_zero
    (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (c : Kˣ) (hc : c ^ p = 1)
    (h1c : IsUnit (1 - (c : K))) :
    ((ModularCurve.tateBase K p).preΨ (p : ℤ)).eval (ModularCurve.tateToricPoint K p c).1 = 0 := by sorry
