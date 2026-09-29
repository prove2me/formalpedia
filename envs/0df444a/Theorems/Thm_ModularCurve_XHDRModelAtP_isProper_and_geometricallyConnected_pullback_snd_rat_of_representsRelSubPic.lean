-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_isProper_and_geometricallyConnected_pullback_snd_rat_of_representsRelSubPic
-- name    : ModularCurve.XHDRModelAtP.isProper_and_geometricallyConnected_pullback_snd_rat_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/2660d9f1-1b71-5e0f-ac73-aad5dfaf7e15
-- title:
--   Properness and geometric connectedness of the generic fibre of Pic⁰
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$, a subgroup $H \le (\mathbb Z/M)^{\times}$, and assume the Laurent series $j$-invariant `jqModC ℚ` lies in the intermediate field `qExpFunctionFieldC ℚ ⊤` of $\mathbb Q((q))$ generated over $\mathbb Q$ by the integral-form ratios for the full group $\mathrm{SL}(2,\mathbb Z)$. Let $\mathfrak X$ be a term of the structure `XHDRModelAtP p M H hpM hj`, which equips the two-chart integral model $X$ of the function field `qExpFunctionFieldC ℚ (ΓM M H)` over $R_p$ with, among other data summarised here, properness, flatness and local finite presentation of its structure morphism `toBase`, integrality and normality of $X$, smoothness and geometric integrality of its base change to $\mathbb Q$, and a geometric curve model over $\overline{\mathbb Q}$ with prescribed Galois action and $q$-expansion pinning; in particular $\mathfrak X$ provides a rigidifying section $\mathfrak X.\varepsilon_{\infty}$ over $\mathrm{Spec}\,R_p$. Let $D$ be a `RelativePic0Designation`, i.e. a scheme with a morphism `D.toBase` to $\mathrm{Spec}\,R_p$ together with a zero section splitting it, and let $hD$ assert that $D$ represents the relative Picard functor of $X$ rigidified along $\mathfrak X.\varepsilon_{\infty}$ cut out by the fibrewise algebraic-equivalence-to-zero condition `algEquivZeroCut`: a Poincaré rigidified line bundle on `D.toBase` satisfying that condition, universal in the sense that every rigidified bundle satisfying it over a base $t$ is, up to isomorphism of underlying bundles, pulled back along a unique morphism over $\mathrm{Spec}\,R_p$, with trivial pullback along the zero section. Assume `D.toBase` is locally of finite type. Then the second projection of the fibre product of `D.toBase` with $\mathrm{Spec}\,\mathbb Q \to \mathrm{Spec}\,R_p$ is proper and geometrically connected.
--
--   The generic fibre of such a representing scheme is the Jacobian of the smooth proper geometrically integral curve $X_H(M)_{\mathbb Q}$, hence an abelian variety; this statement isolates the properness and geometric connectedness of that fibre in the level-$\Gamma_H(M)$ setting. It supplies the properness input to the construction of level data representing the relative Picard functor in [`ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords`](thm.html#ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_isProper_and_geometricallyConnected_pullback_snd_rat_of_representsRelSubPic.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel AlgebraicCurve
open AlgebraicGeometry.RelPicard

open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.isProper_and_geometricallyConnected_pullback_snd_rat_of_representsRelSubPic
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) (𝔛 : XHDRModelAtP p M H hpM hj)
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    [LocallyOfFiniteType D.toBase] :
    IsProper (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) ∧
      GeometricallyConnected (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) := by sorry
