-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_algEquiv_ffEquiv_symm_germToFunctionField_eq_of_pointEquivPlace_eq_ofAlgAut_smul
-- name    : ModularCurve.XHDRModelAtP.algEquiv_ffEquiv_symm_germToFunctionField_eq_of_pointEquivPlace_eq_ofAlgAut_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/af624365-b3c8-5cab-94de-68747229aa9c
-- title:
--   θ acts on functions as pull-back along w
-- statement:
--   Fix a prime $p$, a nonzero modulus $M$ with $p \mid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$, together with a proof `hj` that the $q$-expansion $j$-series `jqModC ℚ` lies in the field `qExpFunctionFieldC ℚ ⊤` generated over $\mathbb{Q}$ by the ratios of integral forms for $\mathrm{SL}(2,\mathbb{Z})$. Let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`; among its data are the two-chart model `X p (ΓM M H) hj` over `R p` with structure morphism `toBase`, an automorphism `𝔛.w`, and a curve model `𝔛.Meta` over $\overline{\mathbb{Q}}$ with function field $\overline{\mathbb{Q}}$-isomorphic via `ffEquiv` to `xHFunctionFieldBar M H`, identified by the isomorphism `𝔛.eeta` with the base change of `X p (ΓM M H) hj` along $R_p \to \overline{\mathbb{Q}}$. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of `xHFunctionFieldBar M H` satisfying the place law `hwgen`: whenever $y,y'$ are sections of `𝔛.Meta.toBase` (i.e. $\overline{\mathbb{Q}}$-points of `𝔛.Meta.C`) such that $y'$ followed by `𝔛.eeta`, the first pullback projection and `𝔛.w.hom` equals $y$ followed by `𝔛.eeta` and that projection, the place `𝔛.Meta.pointEquivPlace y'` — a valuation subring of the function field containing $\overline{\mathbb{Q}}$, proper and with principal ideals — is the translate of `𝔛.Meta.pointEquivPlace y` under the semilinear automorphism `SemilinearAut.ofAlgAut θ` attached to $\theta$ with trivial action on $\overline{\mathbb{Q}}$. Let $U$ be an open of `X p (ΓM M H) hj` and $g \in \Gamma(X p (ΓM M H) hj, U)$, and assume that the preimages of $U$ and of `𝔛.w.hom ⁻¹ᵁ U` under `𝔛.eeta` followed by the first pullback projection are nonempty. Then $\theta$ applied to the element of `xHFunctionFieldBar M H` obtained by pulling $g$ back to the geometric fibre, taking its germ at the generic point and transporting along `𝔛.Meta.ffEquiv.symm`, equals the element obtained in the same way from the pull-back `(𝔛.w.hom.app U).hom g` of $g$ along `𝔛.w`, read over the preimage of `𝔛.w.hom ⁻¹ᵁ U`.
--
--   This upgrades the characterisation of the Atkin–Lehner automorphism $\theta$ of the geometric function field of $X_H(M)$ from its effect on places of $\overline{\mathbb{Q}}$-points to the identity $\theta = w^{*}$ on functions, reading sections of the Deligne–Rapoport model in the function field via restriction to the geometric generic fibre and the germ at its generic point. It is used in the analysis of the crossing points and of the values of functions at the places `placeOn0` and `placeOn1` on the two branches of the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_algEquiv_ffEquiv_symm_germToFunctionField_eq_of_pointEquivPlace_eq_ofAlgAut_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.algEquiv_ffEquiv_symm_germToFunctionField_eq_of_pointEquivPlace_eq_ofAlgAut_smul
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (U : (X p (ΓM M H) hj).Opens)
    (hU : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ U)))
    (hwU : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ U))))
    (g : Γ(X p (ΓM M H) hj, U)) :
    θ (haveI := hU; 𝔛.Meta.ffEquiv.symm
          (𝔛.Meta.C.germToFunctionField ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ U) (((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app U).hom g))) =
      (haveI := hwU; 𝔛.Meta.ffEquiv.symm
          (𝔛.Meta.C.germToFunctionField ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ U))
            (((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app (𝔛.w.hom ⁻¹ᵁ U)).hom ((𝔛.w.hom.app U).hom g)))) := by sorry
