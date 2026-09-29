-- Prove2me | Theorems.Thm_ModularCurve_IsGamma1Point_variableChange_eq_one_of_smul_eq_of_variableChange_eq
-- name    : ModularCurve.IsGamma1Point.variableChange_eq_one_of_smul_eq_of_variableChange_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/9e1daacd-eece-5b86-98c3-fda33afa554b
-- title:
--   Rigidity of Γ₁(ℓ)-points under variable changes
-- statement:
--   Let $T$ be a commutative ring and let $\ell$ be a natural number that is prime, with $5 \le \ell$ and with the image of $\ell$ in $T$ a unit. Let $W$ be a Weierstrass curve over $T$ whose discriminant $W.\Delta$ is a unit, and let $D$ be a `LevelPData T`, that is a quadruple $(x_P, y_P, x_Q, y_Q)$ of elements of $T$, satisfying `IsGamma1Point W ℓ D`: the affine Weierstrass equation of $W$ holds at $(x_P, y_P)$, the $\ell$-th division polynomial $W.preΨ ℓ$ evaluates to $0$ at $x_P$, and $x_Q = x_P$, $y_Q = y_P$ (so the second point is a copy of the first). Let $C$ be a Weierstrass variable change over $T$, given by data $(u, r, s, t)$ with $u$ a unit, and suppose that $C$ fixes the curve, $C \bullet W = W$, and fixes the level data, $D.variableChange C = D$, where the latter acts by $x \mapsto u^{-2}(x - r)$ and $y \mapsto u^{-3}(y - s(x - r) - t)$ on each of the two points. Then $C$ is the identity variable change, $C = 1$.
--
--   This is the rigidity statement for $\Gamma_1(\ell)$-level structures in the style of Katz–Mazur: a $\Gamma_1(\ell)$-point of order a zero of the $\ell$-division polynomial on a smooth Weierstrass curve with $\ell \ge 5$ invertible admits no nontrivial automorphisms of the ambient Weierstrass model. It underlies the construction and counting of moduli packages for the full-level/diamond-operator part of the development, being used in the statements that produce level moduli packages and count points on the relevant moduli.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsGamma1Point_variableChange_eq_one_of_smul_eq_of_variableChange_eq.lean

import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.IsGamma1Point.variableChange_eq_one_of_smul_eq_of_variableChange_eq
    {T : Type u} [CommRing T] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (hℓu : IsUnit ((ℓ : ℕ) : T))
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (D : LevelPData T) (hD : IsGamma1Point W ℓ D)
    (C : WeierstrassCurve.VariableChange T) (hCW : C • W = W) (hCD : D.variableChange C = D) :
    C = 1 := by sorry
