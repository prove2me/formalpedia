-- Prove2me | Theorems.Thm_ModularCurve_IsLevelPStructure_exists_injective_addMonoidHom_zmod_prod
-- name    : ModularCurve.IsLevelPStructure.exists_injective_addMonoidHom_zmod_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/085e35c4-0da6-5be0-b378-03aad19f46fb
-- title:
--   Level-p data yield an injective map (ℤ/p)² → W(F)
-- statement:
--   Let $F$ be a field with decidable equality and let $W$ be a Weierstrass curve over $F$ which is elliptic (invertible discriminant). Let $p$ be a prime with $p \neq 2$, and assume $(p : F) \neq 0$. Let $D$ be a [`ModularCurve.LevelPData F`](def/ModularCurve_KatzLevelP.html#L43), that is a quadruple of elements $x_P, y_P, x_Q, y_Q$ of $F$, and assume [`ModularCurve.IsLevelPStructure W p D`](def/ModularCurve_KatzLevelP.html#L104), which asserts: the pairs $(x_P,y_P)$ and $(x_Q,y_Q)$ both satisfy the affine Weierstrass equation of $W$; the $p$-th division polynomial value $(W.\mathrm{pre\Psi}\,p)$ vanishes at $x_P$ and at $x_Q$; and the two elements $\mathrm{indepElt}(W,p,x_P,x_Q) = \prod_{a=1}^{(p-1)/2}\bigl(x_Q\cdot(W.\Psi\mathrm{Sq}\,a)(x_P) - (W.\Phi\,a)(x_P)\bigr)$ and $\mathrm{indepElt}(W,p,x_Q,x_P)$, obtained by exchanging the roles of $x_P$ and $x_Q$, are both units of $F$. The conclusion is the bare existence of an additive group homomorphism $f : \mathbb{Z}/p \times \mathbb{Z}/p \to W(F)$, where $W(F)$ is the group of points of the affine model of $W$, which is injective; no particular such $f$ is named in the statement.
--
--   The hypothesis [`ModularCurve.IsLevelPStructure`](def/ModularCurve_KatzLevelP.html#L104) is a division-polynomial rendering, in terms of the affine coordinates of two points, of a basis of the $p$-torsion of an elliptic curve in the sense of Drinfeld–Katz–Mazur; the conclusion says that the resulting subgroup of $W(F)$ is free of rank $2$ over $\mathbb{Z}/p$, so that the full $p$-torsion is $F$-rational. It is used in the construction of points on modular curves with full level structure, in [`ModularCurve.FullLevel.exists_pt_laurentBaseChange_jOf_eq_jqNModC_gamma0Pow_of_algebra`](thm.html#ModularCurve.FullLevel.exists_pt_laurentBaseChange_jOf_eq_jqNModC_gamma0Pow_of_algebra).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsLevelPStructure_exists_injective_addMonoidHom_zmod_prod.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.IsLevelPStructure.exists_injective_addMonoidHom_zmod_prod
    {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0)
    {D : ModularCurve.LevelPData F} (hD : ModularCurve.IsLevelPStructure W p D) :
    ∃ f : ZMod p × ZMod p →+ W.toAffine.Point, Function.Injective f := by sorry
