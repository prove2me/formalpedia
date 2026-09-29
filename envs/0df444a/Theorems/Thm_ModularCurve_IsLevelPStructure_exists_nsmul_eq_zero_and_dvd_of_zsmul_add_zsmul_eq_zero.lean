-- Prove2me | Theorems.Thm_ModularCurve_IsLevelPStructure_exists_nsmul_eq_zero_and_dvd_of_zsmul_add_zsmul_eq_zero
-- name    : ModularCurve.IsLevelPStructure.exists_nsmul_eq_zero_and_dvd_of_zsmul_add_zsmul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/a9463fe5-5827-5f2d-a3bf-77aea1a1cc58
-- title:
--   Level-ℓ data gives an independent pair of ℓ-torsion points
-- statement:
--   Let $F$ be a field with decidable equality, let $W$ be a Weierstrass curve over $F$ that is elliptic, and let $\ell$ be a prime with $\ell \neq 2$. Let $D$ consist of four elements $x_P, y_P, x_Q, y_Q$ of $F$, and assume $D$ satisfies [`ModularCurve.IsLevelPStructure W ℓ D`](def/ModularCurve_KatzLevelP.html#L104), i.e.: both $(x_P, y_P)$ and $(x_Q, y_Q)$ satisfy the affine Weierstrass equation of $W$; the $\ell$-th normalised division polynomial $W.\mathrm{preΨ}\ \ell$ vanishes at $x_P$ and at $x_Q$; and the two elements $\prod_{a=1}^{(\ell-1)/2}\bigl(x_Q\,(W.\Psi\mathrm{Sq}\ a)(x_P) - (W.\Phi\ a)(x_P)\bigr)$ and $\prod_{a=1}^{(\ell-1)/2}\bigl(x_P\,(W.\Psi\mathrm{Sq}\ a)(x_Q) - (W.\Phi\ a)(x_Q)\bigr)$ are units of $F$. The conclusion asserts that $(x_P, y_P)$ and $(x_Q, y_Q)$ are nonsingular points, so that they define points $P$ and $Q$ of the affine point group of $W$, and that for these points $\ell \cdot P = 0$, $\ell \cdot Q = 0$, and for all integers $a, b$ the relation $a \cdot P + b \cdot Q = 0$ forces $\ell \mid a$ and $\ell \mid b$ in $\mathbb{Z}$.
--
--   This is the reading over a field of the division-polynomial presentation of a full level-$\ell$ structure: it converts the algebraic data `LevelPData` together with the conditions `IsLevelPStructure` into a genuinely independent pair of $\ell$-torsion points of $W(F)$, generating a subgroup isomorphic to $(\mathbb{Z}/\ell)^2$. It is used in the comparison between level structures for the rigid full-level Weierstrass moduli problem and level structures on points, and thereby in the construction of primitive $\ell$-th roots of unity attached to points of the full-level and $\Gamma_0$-type curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsLevelPStructure_exists_nsmul_eq_zero_and_dvd_of_zsmul_add_zsmul_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.IsLevelPStructure.exists_nsmul_eq_zero_and_dvd_of_zsmul_add_zsmul_eq_zero
    {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (D : ModularCurve.LevelPData F)
    (hD : ModularCurve.IsLevelPStructure W ℓ D) :
    ∃ (hP : W.toAffine.Nonsingular D.xP D.yP) (hQ : W.toAffine.Nonsingular D.xQ D.yQ),
      ℓ • WeierstrassCurve.Affine.Point.some D.xP D.yP hP = 0 ∧
      ℓ • WeierstrassCurve.Affine.Point.some D.xQ D.yQ hQ = 0 ∧
      ∀ a b : ℤ, a • WeierstrassCurve.Affine.Point.some D.xP D.yP hP +
          b • WeierstrassCurve.Affine.Point.some D.xQ D.yQ hQ = 0 → (ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ b := by sorry
