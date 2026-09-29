-- Prove2me | Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaHBar
-- name    : ModularCurve.finrankAlong_heckeAlphaHBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/7c7d82f5-f6b6-5ee3-b0fa-dbf8f9b2db38
-- title:
--   Degree ℓ+1 of the degeneracy map α on function fields
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $M$ be a nonzero natural number, let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$, and let $\ell$ be a prime with $\ell \nmid M$. Consider the $L$-algebra map $\alpha =$ [`ModularCurve.heckeAlphaHBar L M H ℓ`](def/ModularCurve_XHHeckeOperator.html#L66), namely the inclusion of intermediate fields of $L((q))$ from [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M H)`](def/ModularCurve_LaurentCoeff.html#L103) into [`ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))`](def/ModularCurve_LaurentCoeff.html#L103); here for an intermediate field $F_0$ of $\mathbb{Q}((q))$ the field `laurentBaseChange L F₀` is the subfield of $L((q))$ generated over $L$ by the image of $F_0$ under the coefficientwise embedding `coeffEmb L`, the source arises from the intermediate field `xHFunctionFieldC ℚ M H` of $\mathbb{Q}((q))$ attached to $M$ and $H$, and the target arises from `qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))`, the inclusion being the one induced by the containment of the former in the latter. The assertion is that [`AlgebraicCurve.finrankAlong L α`](def/AlgebraicCurve_Correspondence.html#L51), the $L((q))$-target viewed as a module over the source through $\alpha$ and its `Module.finrank` taken, equals $\ell + 1$. Since this rank is nonzero, the extension is in particular finite.
--
--   This computes the degree of the degeneracy covering $X(\Gamma_H(M) \cap \Gamma_0(\ell)) \to X_H(M)$ on the level of $q$-expansion function fields over $L$, the classical value $[\pm\Gamma_H(M) : \pm(\Gamma_H(M)\cap\Gamma_0(\ell))] = \ell+1$ for $\ell \nmid M$. It feeds the construction and the Eichler–Shimura style relations for the Hecke operators on the Jacobian of $X_H$, and the flatness statements for the associated degeneracy pairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaHBar.lean

import Mathlib
import Definitions.Def_ModularCurve_XHHeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.finrankAlong_heckeAlphaHBar (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ)
    [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) :
    AlgebraicCurve.finrankAlong L (ModularCurve.heckeAlphaHBar L M H ℓ) = ℓ + 1 := by sorry
