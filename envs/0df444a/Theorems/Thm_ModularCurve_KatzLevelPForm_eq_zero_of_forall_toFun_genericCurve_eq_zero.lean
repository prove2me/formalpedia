-- Prove2me | Theorems.Thm_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero
-- name    : ModularCurve.KatzLevelPForm.eq_zero_of_forall_toFun_genericCurve_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/f5b80c6c-bd4a-5fd1-97a5-87b7c058be38
-- title:
--   Generic-curve vanishing of a level-p Katz form
-- statement:
--   Let $K$ be a field, let $p$ be a prime with $p \neq 2$ and with $p$ invertible in the sense that $(p : K) \neq 0$, and let $k \in \mathbb{Z}$. Let $G$ be a Katz level-$p$ form of weight $k$ over $K$, that is: a rule `toFun` which to every commutative $K$-algebra $A$, every Weierstrass curve $W$ over $A$ whose discriminant $W.\Delta$ is a unit, and every quadruple $D = (x_P, y_P, x_Q, y_Q)$ of elements of $A$ satisfying `IsLevelPStructure` — both $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine Weierstrass equation of $W$, both $x_P$ and $x_Q$ are roots of $W.\mathrm{pre}\Psi\,p$, and both $\mathrm{indepElt}\,W\,p\,x_P\,x_Q = \prod_{a=1}^{(p-1)/2}\bigl(x_Q\,(W.\Psi\mathrm{Sq}\,a)(x_P) - (W.\Phi\,a)(x_P)\bigr)$ and the same expression with $x_P$ and $x_Q$ interchanged are units — assigns an element of $A$, subject to compatibility with $K$-algebra maps and to the weight-$k$ transformation law $G(C \bullet W, D^{C}) = (u_C^{-1})^{k}\,G(W,D)$ under Weierstrass variable changes $C$. Let $\Omega$ be an algebraic closure of the fraction field of $K[X_0,\dots,X_4]$ and let $E$ over $\Omega$ be the generic Weierstrass curve $\mathrm{curve}\,K$ with coefficients the images of $X_0,\dots,X_4$, whose discriminant is a unit. If $G(E, D) = 0$ for every quadruple $D$ over $\Omega$ that is a level-$p$ structure on $E$, then $G = 0$.
--
--   This is the statement that a Katz modular form of full level $p$ is determined by its values on level-$p$ structures of the geometric generic fibre of the universal Weierstrass family, reflecting the representability and étaleness of the level-$p$ moduli problem in characteristic prime to $p$. It is used to reduce vanishing statements for level-$p$ forms over a field to computations at the cusp, and is cited in that shape by [`ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_field`](thm.html#ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_field) and [`ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field`](thm.html#ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_WeierstrassCurve_Generic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.KatzLevelPForm.eq_zero_of_forall_toFun_genericCurve_eq_zero
    {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : (p : K) ≠ 0) {k : ℤ}
    (G : ModularCurve.KatzLevelPForm K p k)
    (h : ∀ (D : ModularCurve.LevelPData (WeierstrassCurve.Generic.Closure K))
      (hD : ModularCurve.IsLevelPStructure (WeierstrassCurve.Generic.curve K) p D),
      G.toFun (WeierstrassCurve.Generic.curve K) (WeierstrassCurve.Generic.isUnit_Δ_curve K) D hD = 0) :
    G = 0 := by sorry
