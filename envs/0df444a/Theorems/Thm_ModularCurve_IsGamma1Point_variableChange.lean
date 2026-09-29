-- Prove2me | Theorems.Thm_ModularCurve_IsGamma1Point_variableChange
-- name    : ModularCurve.IsGamma1Point.variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/cfecc386-a198-51b7-81f4-c217aa318279
-- title:
--   Invariance of Γ₁(ℓ)-point data under Weierstrass coordinate changes
-- statement:
--   Let $A$ be a commutative ring, $W$ a Weierstrass curve over $A$, $\ell$ a natural number, and $D$ a [`ModularCurve.LevelPData A`](def/ModularCurve_KatzLevelP.html#L43), that is a quadruple of elements $x_P, y_P, x_Q, y_Q$ of $A$. Assume [`ModularCurve.IsGamma1Point W ℓ D`](def/ModularCurve_WeierstrassGamma1Pow.html#L10), i.e. the four conditions: $(x_P, y_P)$ satisfies the affine Weierstrass equation of $W$; the $\ell$-th division polynomial $\psi_\ell$ of $W$, in the form `W.preΨ ℓ`, vanishes when evaluated at $x_P$; and $x_Q = x_P$, $y_Q = y_P$. Let $C = (u, r, s, t)$ be an admissible change of Weierstrass coordinates over $A$ (with $u$ a unit). Then [`ModularCurve.IsGamma1Point`](def/ModularCurve_WeierstrassGamma1Pow.html#L10) holds for the transformed data as well: writing $C \bullet D$ for the quadruple with $x' = (u^{-1})^2 (x - r)$ and $y' = (u^{-1})^3\bigl(y - s(x - r) - t\bigr)$ applied to both the $P$- and the $Q$-coordinates of $D$, the point $(x'_P, y'_P)$ satisfies the affine equation of the transformed curve $C \bullet W$, the polynomial $(C \bullet W).\mathrm{preΨ}\ \ell$ vanishes at $x'_P$, and $x'_Q = x'_P$, $y'_Q = y'_P$. No hypothesis is imposed on $\ell$ or on the discriminant of $W$.
--
--   This is the statement that the notion of a $\Gamma_1(\ell)$-point, recorded in division-polynomial coordinates, depends only on the isomorphism class of the pair (Weierstrass curve, level datum) and not on the chosen Weierstrass model; the vanishing of $\mathrm{preΨ}_\ell$ transforms correctly because $\psi_\ell$ is isobaric of weight $\ell^2 - 1$. It is used throughout the construction of level structures on modular curves, in particular when local data at a point are compared after normalising the Weierstrass model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsGamma1Point_variableChange.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.IsGamma1Point.variableChange {A : Type*} [CommRing A] {W : WeierstrassCurve A} {ℓ : ℕ}
    {D : ModularCurve.LevelPData A} (h : ModularCurve.IsGamma1Point W ℓ D)
    (C : WeierstrassCurve.VariableChange A) :
    ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C) := by sorry
