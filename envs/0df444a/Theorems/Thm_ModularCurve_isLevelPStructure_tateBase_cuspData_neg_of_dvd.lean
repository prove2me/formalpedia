-- Prove2me | Theorems.Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_neg_of_dvd
-- name    : ModularCurve.isLevelPStructure_tateBase_cuspData_neg_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/689380e4-1ae9-5445-9b3f-85fd3b3e1bf1
-- title:
--   Inverse-twisted cusp data gives a level-p structure on Tate(qⁿ)
-- statement:
--   Let $R$ be a commutative ring, $p$ a prime with $p \neq 2$ whose image in $R$ is a unit, and $n$ a nonzero natural number divisible by $p$; write $m = n/p$ for the natural-number quotient. Let $\zeta \in R^{\times}$ satisfy $\sum_{i<p} (\zeta^{m})^{i} = 0$ in $R$. Consider the Weierstrass curve [`ModularCurve.tateBase R n`](def/ModularCurve_TateSlots.html#L46) over the Laurent series $R((q))$, namely the Tate curve obtained from the universal Tate curve over $\mathbb{Z}((q))$ by base change to $R((q))$ followed by the exponent-scaling ring map $q \mapsto q^{n}$, and the level data $D =$ [`ModularCurve.cuspData R n ζ v w`](def/ModularCurve_KatzLevelPCusps.html#L71) attached to the vectors $v = (m \bmod n,\,0)$ and $w = (0,\,-(m \bmod n))$ in $(\mathbb{Z}/n)^{2}$: since the second entry of $v$ vanishes, $(x_P,y_P)$ is the toric point `tateToricPoint R n` with parameter $\zeta^{(m \bmod n).val}$, while $(x_Q,y_Q)$ is the non-toric point `nonToricPoint R n` with parameter $\zeta^{0}$ and exponent the representative of $-(m \bmod n)$ in $\{0,\dots,n-1\}$. The assertion is that $D$ satisfies `IsLevelPStructure` for $p$: both pairs $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine Weierstrass equation of the curve, both abscissae are roots of $\operatorname{pre}\Psi_p$, and the two independence elements $\prod_{a=1}^{(p-1)/2}\bigl(x_Q\,\Psi^{2}_{a}(x_P) - \Phi_{a}(x_P)\bigr)$ and $\prod_{a=1}^{(p-1)/2}\bigl(x_P\,\Psi^{2}_{a}(x_Q) - \Phi_{a}(x_Q)\bigr)$ are units of $R((q))$.
--
--   This records, in division-polynomial form, the classical description of the $p$-torsion of the Tate curve with parameter $q^{n}$: the pair of points with multiplicative parameters $\zeta^{n/p}$ and $q^{-n/p}$ is a basis of $\mathrm{Tate}(q^{n})[p]$ over $R((q))$. It is the variant of the corresponding statement for the parameters $(\zeta^{n/p}, q^{n/p})$ in which the second point is replaced by its inverse, and it feeds the constructions of sections and variable changes over the cusps in the full-level setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_neg_of_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.isLevelPStructure_tateBase_cuspData_neg_of_dvd
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : IsUnit (p : R))
    (n : ℕ) [NeZero n] (hn : p ∣ n)
    (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, ((ζ : R) ^ (n / p)) ^ i = 0) :
    ModularCurve.IsLevelPStructure (ModularCurve.tateBase R n) p
      (ModularCurve.cuspData R n ζ ![((n / p : ℕ) : ZMod n), 0] ![0, -((n / p : ℕ) : ZMod n)]) := by sorry
