-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffEmb
-- name    : ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffEmb
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/4196a6ba-1dfd-54ae-8555-f3b609169017
-- title:
--   q-expansions on the pole chart of the Deligne–Rapoport model
-- statement:
--   Let $p$ be a prime, let $M$ be a nonzero natural number with $p \mid M$, let $H \le (\mathbb{Z}/M)^{\times}$, and assume $\mathrm{jqModC}\ \mathbb{Q}$, the series $q^{-1}$ times the integral power series $\mathrm{jNum}$, lies in $\mathrm{qExpFunctionFieldC}\ \mathbb{Q}\ \top$, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral form ratios for $\mathrm{SL}(2,\mathbb{Z})$. Let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`, so in particular it provides a curve model $\mathfrak{X}.\mathrm{Meta}$ of $\mathrm{xHFunctionFieldBar}\ M\ H$ (the base change to $\overline{\mathbb{Q}}$, inside $\overline{\mathbb{Q}}((q))$, of the function field of $X_H(M)$) over $\overline{\mathbb{Q}}$, an isomorphism $\mathfrak{X}.\mathrm{eeta}$ of $\mathfrak{X}.\mathrm{Meta}.C$ with the fibre product of $\mathrm{toBase}$ and $\operatorname{Spec}$ of $R_p \to \overline{\mathbb{Q}}$, and the field `Meta_pin` asserting the conclusion below for the $j$-finite chart. Assume the preimage under $\mathfrak{X}.\mathrm{eeta}$ followed by the first projection of the open image of $\iota_{\inf}$ is non-empty. Then for every $a$ in $\mathrm{chartAlgInf}\ p\ (\Gamma_M(M,H))\ hj$, the section obtained from $a$ over that preimage open, read as a germ in the function field of $\mathfrak{X}.\mathrm{Meta}.C$ and transported by $\mathfrak{X}.\mathrm{Meta}.\mathrm{ffEquiv}^{-1}$ into $\mathrm{xHFunctionFieldBar}\ M\ H$, equals, as a Laurent series over $\overline{\mathbb{Q}}$, the coefficientwise image $\mathrm{coeffEmb}$ of the $q$-expansion of $a$ in $\mathbb{Q}((q))$.
--
--   This is the $j$-infinite (pole) chart analogue of the structure field `Meta_pin` of `XHDRModelAtP`, which records the same compatibility for the $j$-finite chart: on the geometric generic fibre of the Deligne–Rapoport model, functions of either integral chart are read in the function field as the coefficientwise extensions of their $q$-expansions. It is used to identify cusps with non-affine places and to compute places attached to sections of the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffEmb.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_inf_eq_coeffEmb
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)))]
    (a : ↥(chartAlgInf p (ΓM M H) hj)) :
    ((𝔛.Meta.ffEquiv.symm
        (𝔛.Meta.C.germToFunctionField
          ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
            ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))
          (((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app
              ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom
            (((ιInf p (ΓM M H) hj).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv a))))
        : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := by sorry
