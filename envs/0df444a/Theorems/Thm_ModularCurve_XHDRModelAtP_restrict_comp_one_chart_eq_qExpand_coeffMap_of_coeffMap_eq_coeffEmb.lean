-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_restrict_comp_one_chart_eq_qExpand_coeffMap_of_coeffMap_eq_coeffEmb
-- name    : ModularCurve.XHDRModelAtP.restrict_comp_one_chart_eq_qExpand_coeffMap_of_coeffMap_eq_coeffEmb
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/53cefb16-72c7-55f6-acb3-fcb67de30d94
-- title:
--   Chart function restricted to the Σ⁰ component reads ̄ y(qᵖ)
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb Z/M)^\times$ containing every unit whose image in $(\mathbb Z/(M/p))^\times$ is $1$, with $M/p$ nonzero, and assume the $j$-series `jqModC ℚ` lies in the $q$-expansion function field `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak X$ be a Deligne–Rapoport model datum `XHDRModelAtP p M H hpM hj`, let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ be a ring homomorphism compatible with the structure map $R_p \to \overline{\mathbb Q}$. Further data are an $\overline{\mathbb Q}$-algebra automorphism $\theta$ of `xHFunctionFieldBar M H`, a place-specialisation datum `Psp` and a prolongation datum `Rpd` for `Psp` and $\theta$. Finally let $b$ lie in the finite chart algebra `chartAlgFin p (ΓN p M H hpM) hj` and let $y \in \kappa$-free Laurent series over $A$, i.e. $y \in A((q))$, be a coefficientwise lift of the $q$-expansion of $b$: applying the coefficientwise map induced by $A \hookrightarrow \overline{\mathbb Q}$ to $y$ gives the image in $\overline{\mathbb Q}((q))$ of $b \in \mathbb Q((q))$. Write `bcA` for the base-change morphism from the fibre over $\kappa$ to $X_O =$ the pullback of the model over $\operatorname{Spec} A$ induced by the residue map $A \to \kappa$, $V$ for the preimage under the first pullback projection of the open image of the finite chart `ιFin p (ΓM M H) hj`, and $g_b \in \Gamma(X_O, V)$ for the pullback along that projection of the section of the finite chart corresponding to $\mathfrak X.\mathrm{iota0}\,b$ (two further local abbreviations, the base change $X_{\overline{\mathbb Q}}$ of the model to $\overline{\mathbb Q}$ and the morphism $X_{\overline{\mathbb Q}} \to X_O$ induced by $A \hookrightarrow \overline{\mathbb Q}$, do not occur in the assertion). The conclusion is that the generic point of the curve $C$ underlying $\mathfrak X.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho$, which is integral, lies in the preimage of $V$ under `𝔛.efib` followed by `𝔛.comp … 1` followed by `bcA`, and that the germ at this generic point of the pullback of $g_b$ along that composite, transported by the inverse of the identification `ffEquiv` of the function field of $C$ with $\mathrm{Fbar} =$ `qExpFunctionFieldC κ (ΓN p M H hpM)` and read inside $\kappa((q))$, equals `qExpand κ p` applied to the coefficientwise reduction of $y$, that is the series obtained from $\bar y$ by multiplying all exponents by $p$, $\bar y(q^p)$.
--
--   On the component of the mod-$p$ fibre of the Deligne–Rapoport model of $X_H(M)$ indexed by $1$, the degeneracy map down to level $M/p$ is the relative Frobenius, so a chart function of the lower level pulled back and restricted to this component has its $q$-expansion replaced by the $q^p$-substitution of its reduction. The statement is the form of this reading used to show that certain germs are non-zero units along the component, via [`ModularCurve.XHDRModelAtP.ne_xiZero_of_forall_isUnit_germ_iff_residue_ne_zero`](thm.html#ModularCurve.XHDRModelAtP.ne_xiZero_of_forall_isUnit_germ_iff_residue_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_restrict_comp_one_chart_eq_qExpand_coeffMap_of_coeffMap_eq_coeffEmb.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
  ModularCurve.JZeroNeronObjectAtP MvPolynomial
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.restrict_comp_one_chart_eq_qExpand_coeffMap_of_coeffMap_eq_coeffEmb
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A)
    (hy : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
    letI V : (XO (ΓM M H) hj ρ).Opens :=
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)
    letI gb : Γ(XO (ΓM M H) hj ρ, V) :=
      ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
        (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv (𝔛.iota0 b)))
    letI := (𝔛.Mfib A hA ρ hρ).isIntegral
    ∃ hg₁ : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA) ⁻¹ᵁ V,
      (((𝔛.Mfib A hA ρ hρ).ffEquiv.symm
          (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA) ⁻¹ᵁ V) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₁)
            (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA).app V).hom gb)) : JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
        qExpand (IsLocalRing.ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) y) := by sorry
