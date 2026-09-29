-- Prove2me | Theorems.Thm_ModularCurve_IsGamma1Point_existsUnique_variableChange_isNormalForm
-- name    : ModularCurve.IsGamma1Point.existsUnique_variableChange_isNormalForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/fc2f1400-b301-5ecd-aaae-b57e70ea2cf7
-- title:
--   Unique Tate normal form for a Γ₁(ℓ)-point
-- statement:
--   Let $T$ be a commutative ring, let $\ell$ be a prime with $5 \le \ell$, and let $W$ be a Weierstrass curve over $T$ whose discriminant satisfies that $\ell \cdot \Delta(W)$ is a unit of $T$. Let $D$ be a level-$p$ datum over $T$, that is, a quadruple $(x_P, y_P, x_Q, y_Q)$ of elements of $T$, and assume `IsGamma1Point W ℓ D`: the pair $(x_P, y_P)$ satisfies the affine Weierstrass equation of $W$, the division polynomial $W.\mathrm{preΨ}\,\ell$ vanishes at $x_P$, and the second point is a copy of the first, $x_Q = x_P$ and $y_Q = y_P$. The conclusion is that there is exactly one Weierstrass variable change $C = (u, r, s, t)$ over $T$ for which the transformed pair $(C \bullet W, D.\mathrm{variableChange}\,C)$ — where the transformed datum has first point $\bigl(u^{-2}(x_P - r),\ u^{-3}(y_P - s(x_P-r) - t)\bigr)$ and likewise for the second — satisfies `IsNormalForm ℓ`. Since $\ell$ is a prime with $\ell \ge 5$, the case distinction in `IsNormalForm` at $\ell = 3$ is inactive, so the condition required of the unique $C$ is: $(C \bullet W).a_4 = 0$, $(C \bullet W).a_6 = 0$, $(C \bullet W).a_2 = (C \bullet W).a_3$, and the transformed first point is $(0,0)$; the transformed second point is unconstrained.
--
--   This is the existence and uniqueness of the Tate normal form $E(b,c) : y^2 + (1-c)xy - by = x^3 - bx^2$ with the marked point at the origin, for a Weierstrass curve over an arbitrary base in which $\ell\Delta$ is invertible together with an $\ell$-division point. It serves as the rigidification step for $\Gamma_1(\ell)$-data: the normal form provides the canonical coordinates used in the construction of level moduli packages and in the rigidity statement that a variable change fixing a curve and its normalised datum is trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsGamma1Point_existsUnique_variableChange_isNormalForm.lean

import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelNormalForm
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.IsGamma1Point.existsUnique_variableChange_isNormalForm
    {T : Type u} [CommRing T] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (W : WeierstrassCurve T) (hu : IsUnit ((ℓ : T) * W.Δ)) (D : LevelPData T) (hD : IsGamma1Point W ℓ D) :
    ∃! C : WeierstrassCurve.VariableChange T, IsNormalForm ℓ (C • W) (D.variableChange C) := by sorry
