-- Prove2me | Theorems.Thm_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero
-- name    : ModularCurve.eval_prePsi_tateBase_nonToricPoint_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/c50a43d2-7591-58b5-aa0b-c0ebfe6c3f72
-- title:
--   Vanishing of preΨₚ at the Tate slot abscissa
-- statement:
--   Let $K$ be a commutative ring, $p$ a prime with $p \neq 2$, $c \in K^{\times}$ a unit satisfying $c^{p} = 1$, and $j$ a natural number with $0 < j < p$. Consider the Weierstrass curve [`ModularCurve.tateBase K p`](def/ModularCurve_TateSlots.html#L46) over the Laurent series field-or-ring $K((q))$: it is obtained from the universal Tate coefficients `tatePowerSeries` over $\mathbb{Z}$, transported into $K((q))$ by `laurentOfInt K`, and then pushed along the ring homomorphism `qExpand K p`, which multiplies all Hahn-series exponents by $p$, i.e. substitutes $q \mapsto q^{p}$. Consider also the first coordinate of [`ModularCurve.nonToricPoint K p c j`](def/ModularCurve_TateSlots.html#L35), namely the Laurent series attached to the power series `slotSubst K p c j tateUnivX`, the result of substituting the family `slotFamily K p c j` into the two-variable integral power series `tateUnivX`, whose coefficient at an exponent vector $e$ is $-2\sum_{d \mid e_1} d$ when $e_0 = e_1$ and otherwise is $|e_0 - e_1|$ if $|e_0 - e_1|$ divides $e_1$ and $0$ if not. The assertion is that the univariate polynomial $\mathrm{pre}\Psi_{p}$ of this curve, Mathlib's `preΨ` at the integer $p$, evaluates to $0$ at that Laurent series. Thus the statement is an identity of Laurent series about an abscissa and a division-polynomial factor, not an assertion about a point of a group; in particular $K$ is only a commutative ring and no nonsingularity or ellipticity hypothesis enters.
--
--   This is the algebraic form, valid over an arbitrary commutative ring, of the classical fact that the point $u = c\,q^{j}$ with $c^{p} = 1$ and $0 < j < p$ is $p$-torsion on the Tate curve with parameter $q^{p}$, the abscissa being a root of the $p$-th division polynomial. It is used in the construction of the level-$p$ structures on the Tate base curve attached to the cusps, via [`ModularCurve.LevelP.quotientByLine_tateBase_nonToricPoint_fst`](thm.html#ModularCurve.LevelP.quotientByLine_tateBase_nonToricPoint_fst), [`ModularCurve.isLevelPStructure_tateBase_cuspData_mazurCusp`](thm.html#ModularCurve.isLevelPStructure_tateBase_cuspData_mazurCusp) and [`ModularCurve.isLevelPStructure_tateBase_cuspData_neg_of_dvd`](thm.html#ModularCurve.isLevelPStructure_tateBase_cuspData_neg_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eval_prePsi_tateBase_nonToricPoint_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.eval_prePsi_tateBase_nonToricPoint_eq_zero
    (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (c : Kˣ) (hc : c ^ p = 1)
    (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    ((ModularCurve.tateBase K p).preΨ (p : ℤ)).eval (ModularCurve.nonToricPoint K p c j).1 = 0 := by sorry
