-- Prove2me | Theorems.Thm_ModularCurve_IsGamma0PowAt_variableChange
-- name    : ModularCurve.IsGamma0PowAt.variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/807a7838-2323-559e-b5d4-772aeb45721b
-- title:
--   Invariance of the (p,k)-kernel predicate under variable change
-- statement:
--   Let $T$ be a commutative ring, $W$ a Weierstrass curve over $T$, $C$ a Weierstrass variable change over $T$ (data $u \in T^\times$, $r,s,t \in T$), $p,k$ natural numbers and $h \in T[X]$. Assume [`ModularCurve.IsGamma0PowAt W p k h`](def/ModularCurve_WeierstrassGamma0Pow.html#L55), that is: if $p^k = 2$ then $h$ satisfies `W.IsTwoKernel`, i.e. $\deg h \le 1$, the coefficient of $h$ in degree $1$ is $1$, and $h \mid$ `W.Ψ₂Sq`; while if $p^k \ne 2$ then $h$ satisfies `W.IsCyclicGenKernel p k`, i.e. with $d = \varphi(p^k)/2$ (integer division) one has $\deg h \le d$, the coefficient of $h$ in degree $d$ equals $1$, the divisibility $h \cdot W.\mathrm{pre}\Psi(p^{k-1}) \mid W.\mathrm{pre}\Psi(p^k)$ (with $k-1$ truncated subtraction), and $h \mid$ `W.smulNumerator a d h` for every natural $a$ with $2 \le a \le (p^k-1)/2$ and $p \nmid a$. The conclusion is that the transported polynomial $u^{-2\delta}\, h(u^2X + r)$, where $\delta =$ [`ModularCurve.gamma0PowDeg p k`](def/ModularCurve_WeierstrassGamma0Pow.html#L53) is $1$ if $p^k = 2$ and $\varphi(p^k)/2$ otherwise, satisfies the same predicate [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) for the curve $C \bullet W$, with the same $p$ and $k$.
--
--   This is the compatibility of the $(p,k)$-component of a level structure, recorded as a generating kernel polynomial, with Weierstrass changes of variables; it is what allows such components to be glued into data attached to the curve rather than to a chosen Weierstrass model. It is used throughout the construction of the level-$p^k$ moduli packages and their automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsGamma0PowAt_variableChange.lean

import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.IsGamma0PowAt.variableChange
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T) (p k : ℕ)
    (h : Polynomial T) (hh : ModularCurve.IsGamma0PowAt W p k h) :
    ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h) := by sorry
