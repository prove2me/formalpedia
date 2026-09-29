-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_existsUnique_hom_comp_toBase_eq_and_specMap_comp_eq_of_point
-- name    : ModularCurve.XHDRModelAtP.existsUnique_hom_comp_toBase_eq_and_specMap_comp_eq_of_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/bb9ce32e-a4a6-5be2-8b03-508eb98fee0a
-- title:
--   Unique extension of ℚ̄-points over valuation rings
-- statement:
--   Fix a prime $p$ and a non-zero natural number $M$ with $p \mid M$, a subgroup $H$ of $(\mathbb{Z}/M)^{\times}$, and a witness $hj$ that the Laurent series `jqModC ℚ` (the $q$-expansion of $j$, namely $q^{-1}$ times the integral power series `jNum`) lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios of integral $q$-expansions of modular forms for $\mathrm{SL}(2,\mathbb{Z})$. Let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`, the bundle of properties of the two-chart integral model `X p (ΓM M H) hj` over $\operatorname{Spec}(R_p)$ — properness, flatness, integrality and local finite presentation of the structure morphism `toBase`, normality of the sections over affine opens, properness and relative-dimension-one smoothness at the auxiliary level `ΓN p M H hpM`, a geometric curve model for the base change to $\overline{\mathbb{Q}}$ together with its identification `eeta`, Galois equivariance, chart normalisation and generic-fibre conditions, all summarised here. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $\rho \colon R_p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $R_p \to \overline{\mathbb{Q}}$, and let $x \colon \operatorname{Spec}(\overline{\mathbb{Q}}) \to$ `X p (ΓM M H) hj` be a morphism lying over $\operatorname{Spec}$ of that structure map. Then there is exactly one morphism $s \colon \operatorname{Spec}(A) \to$ `X p (ΓM M H) hj` lying over $\operatorname{Spec}(\rho)$ and restricting along $\operatorname{Spec}$ of $A \hookrightarrow \overline{\mathbb{Q}}$ to $x$.
--
--   This is the valuative criterion of properness applied to the Deligne–Rapoport type model of $X_H(M)$ over $R_p$: a $\overline{\mathbb{Q}}$-point of the model spreads out uniquely to a section over any valuation subring of $\overline{\mathbb{Q}}$ with compatible structure map. It is what allows a $\overline{\mathbb{Q}}$-point, equivalently a place of the function field, to be given a reduction and a horizontal divisor over $A$, and it feeds the computation of orders of vanishing at places of the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_existsUnique_hom_comp_toBase_eq_and_specMap_comp_eq_of_point.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.existsUnique_hom_comp_toBase_eq_and_specMap_comp_eq_of_point
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (x : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X p (ΓM M H) hj)
    (hx : x ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) :
    ∃! s : Spec (CommRingCat.of ↥A) ⟶ X p (ΓM M H) hj,
      s ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom ρ) ∧
        Spec.map (CommRingCat.ofHom A.subtype) ≫ s = x := by sorry
