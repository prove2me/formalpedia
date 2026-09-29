-- Prove2me | Theorems.Thm_ModularCurve_IsLevelPStructure_exists_eq_nsmul_add_nsmul_of_isLevelPStructure
-- name    : ModularCurve.IsLevelPStructure.exists_eq_nsmul_add_nsmul_of_isLevelPStructure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/dd277560-1822-5da5-9fbb-5d4c9138da15
-- title:
--   Two level-ℓ structures differ by an invertible matrix
-- statement:
--   Let $F$ be a field, let $\ell$ be a prime with $3 \le \ell$ and with $\ell \neq 0$ in $F$, and let $W$ be a Weierstrass curve over $F$ whose discriminant $\Delta$ is a unit. Let $D_1, D_2$ be two elements of `LevelPData F`, each consisting of four field elements $x_P, y_P, x_Q, y_Q$, and suppose each $D_i$ satisfies `IsLevelPStructure W ℓ`, that is: both pairs $(x_P, y_P)$ and $(x_Q, y_Q)$ satisfy the affine Weierstrass equation of $W$; the polynomial $W.\mathrm{pre}\Psi\,\ell$ vanishes at $x_P$ and at $x_Q$; and both independence elements $\mathrm{indepElt}\,W\,\ell\,x_P\,x_Q$ and $\mathrm{indepElt}\,W\,\ell\,x_Q\,x_P$ are units, where $\mathrm{indepElt}\,W\,\ell\,x_0\,x = \prod_{a=1}^{(\ell-1)/2}\bigl(x\,(W.\Psi\mathrm{Sq}\,a)(x_0) - (W.\Phi\,a)(x_0)\bigr)$. The conclusion asserts the existence of nonsingularity witnesses for all four coordinate pairs, so that each gives an affine point of $W$, together with $a, b, c, d \in \mathbb{Z}/\ell$ with $ad - bc \neq 0$ such that, writing $P_i, Q_i$ for the affine points attached to $D_i$ and taking natural-number representatives of the scalars, $P_2 = a P_1 + b Q_1$ and $Q_2 = c P_1 + d Q_1$ in the group of points of $W$.
--
--   This is the statement that the level-$\ell$ structures in the sense of the predicate `IsLevelPStructure` on a fixed elliptic curve over a field form a single $\mathrm{GL}_2(\mathbb{Z}/\ell)$-orbit, the two given structures being related by an invertible relabelling matrix. It is used in the comparison of rational points of the full-level moduli problem, notably in the determinant computations for relabellings and in the passage between level structures with equal Weil pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsLevelPStructure_exists_eq_nsmul_add_nsmul_of_isLevelPStructure.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.IsLevelPStructure.exists_eq_nsmul_add_nsmul_of_isLevelPStructure
    {F : Type u} [Field F] [DecidableEq F] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓF : (ℓ : F) ≠ 0)
    (W : WeierstrassCurve F) (hΔ : IsUnit W.Δ)
    (D₁ D₂ : LevelPData F) (h₁ : IsLevelPStructure W ℓ D₁) (h₂ : IsLevelPStructure W ℓ D₂) :
    ∃ (n₁P : W.toAffine.Nonsingular D₁.xP D₁.yP) (n₁Q : W.toAffine.Nonsingular D₁.xQ D₁.yQ)
      (n₂P : W.toAffine.Nonsingular D₂.xP D₂.yP) (n₂Q : W.toAffine.Nonsingular D₂.xQ D₂.yQ)
      (a b c d : ZMod ℓ), a * d - b * c ≠ 0 ∧
      WeierstrassCurve.Affine.Point.some _ _ n₂P =
        a.val • WeierstrassCurve.Affine.Point.some _ _ n₁P + b.val • WeierstrassCurve.Affine.Point.some _ _ n₁Q ∧
      WeierstrassCurve.Affine.Point.some _ _ n₂Q =
        c.val • WeierstrassCurve.Affine.Point.some _ _ n₁P + d.val • WeierstrassCurve.Affine.Point.some _ _ n₁Q := by sorry
