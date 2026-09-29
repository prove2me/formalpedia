-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_residue_readA_chart_eq_and_restrict_comp_zero_chart_eq_coeffMap_of_coeffMap_eq_coeffEmb
-- name    : ModularCurve.XHDRModelAtP.residue_readA_chart_eq_and_restrict_comp_zero_chart_eq_coeffMap_of_coeffMap_eq_coeffEmb
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/961fbd63-d802-51f3-8760-7f245011c042
-- title:
--   Chart function readings agree with the reduced q-expansion
-- statement:
--   Fix a prime $p$ and a nonzero $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$, with $M/p$ nonzero, and assume $j$, in the shape of the Laurent series `jqModC ℚ`, lies in the $q$-expansion function field of full level; let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ be a ring homomorphism compatible with the structure map $R_p \to \overline{\mathbb{Q}}$. Let $\theta$ be an $\overline{\mathbb{Q}}$-algebra automorphism of $\overline{F}_{M,H} =$ `xHFunctionFieldBar M H`, let `Psp` be a place-specialisation datum for $(p,M,H,A)$ and `Rpd` a prolongation datum for `Psp` and $\theta$, with regular prolongations $R_1, R_2$ of $A$ in $\overline{F}_{M,H}$ with values in $\bar F =$ `qExpFunctionFieldC` of level $\Gamma_N(p,M,H)$ over the residue field $\kappa$ of $A$. Let $b$ lie in the $j$-finite chart algebra of level $\Gamma_N(p,M,H)$ over $R_p$, and let $y \in \kappa$-free form, namely $y \in A((q))$, be a coefficientwise lift of the $q$-expansion of $b$: applying the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ to the coefficients of $y$ gives the image of $b$'s Laurent series under $\mathbb{Q} \hookrightarrow \overline{\mathbb{Q}}$. Write $X_{\overline{\mathbb{Q}}}$ for the base change of the model of level $\Gamma_M(M,H)$ along $R_p \to \overline{\mathbb{Q}}$, $\mathrm{pr}_A$ for the induced morphism to the base change $X_A$ along $\rho$ coming from $A \hookrightarrow \overline{\mathbb{Q}}$, and $\mathrm{bc}_A$ for the morphism from the fibre over $\kappa$ to $X_A$ induced by the residue map of $A$. Let $V \subseteq X_A$ be the preimage under the first projection of the image of the $j$-finite chart, and let $g_b \in \Gamma(X_A, V)$ be the section obtained from the global section of the affine $j$-finite chart determined by $\mathfrak{X}.\mathrm{iota0}\,b$. The assertion is that the point $\mathfrak{X}.\xi_{\inf}$ attached to $A, \rho$ and the residue map lies in $V$, that the generic point of the curve $\mathfrak{X}.\mathrm{Meta}.C$ lies in the preimage of $V$ under $\mathfrak{X}.\mathrm{eeta}$ followed by $\mathrm{pr}_A$, and, with $\mathrm{read}_A : \Gamma(X_A,V) \to \overline{F}_{M,H}$ the ring homomorphism given by pulling back along $\mathrm{pr}_A$ and $\mathfrak{X}.\mathrm{eeta}$, taking the germ at that generic point and transporting through $\mathfrak{X}.\mathrm{Meta}.\mathrm{ffEquiv}^{-1}$, that both of the following hold: (i) $\mathrm{read}_A(g_b)$ lies in the valuation subring $R_1.\mathrm{integers}$ and its $R_1$-residue, viewed as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$; (ii) the generic point of $(\mathfrak{X}.\mathrm{Mfib})$'s curve lies in the preimage of $V$ under $\mathfrak{X}.\mathrm{efib}$ followed by $\mathfrak{X}.\mathrm{comp}\,0$ followed by $\mathrm{bc}_A$, and the element of $\bar F$ obtained by pulling $g_b$ back along that composite, taking the germ there and transporting through the corresponding $\mathrm{ffEquiv}^{-1}$, has the same Laurent expansion, the coefficientwise reduction of $y$.
--
--   This is the dictionary step identifying the two ways of reading a $j$-finite chart function on the Deligne–Rapoport model after base change to a valuation ring $A$ above $p$: through the generic fibre and the first Gauss prolongation $R_1$, and through restriction to the component indexed by $0$ of the fibre over the residue field; both give the reduced $q$-expansion. It is used by [`ModularCurve.XHDRModelAtP.ne_xiZero_of_forall_isUnit_germ_iff_residue_ne_zero`](thm.html#ModularCurve.XHDRModelAtP.ne_xiZero_of_forall_isUnit_germ_iff_residue_ne_zero) and [`ModularCurve.XHDRModelAtP.residue_readA_eq_restrict_comp_zero_of_forall_isUnit_germ_iff_residue_ne_zero`](thm.html#ModularCurve.XHDRModelAtP.residue_readA_eq_restrict_comp_zero_of_forall_isUnit_germ_iff_residue_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_residue_readA_chart_eq_and_restrict_comp_zero_chart_eq_coeffMap_of_coeffMap_eq_coeffEmb.lean

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

theorem ModularCurve.XHDRModelAtP.residue_readA_chart_eq_and_restrict_comp_zero_chart_eq_coeffMap_of_coeffMap_eq_coeffEmb
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
    ∃ (hi : 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ V)
      (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)),
    letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
        (𝔛.Meta).ffEquiv.symm.toRingHom.comp
          (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
            ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
    (∃ h : readA gb ∈ Rpd.R₁.integers,
      ((Rpd.R₁.residue ⟨readA gb, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
        coeffMap (IsLocalRing.residue ↥A) y) ∧
    letI := (𝔛.Mfib A hA ρ hρ).isIntegral
    (∃ hg₀ : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ V,
      (((𝔛.Mfib A hA ρ hρ).ffEquiv.symm
          (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ V) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₀)
            (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).app V).hom gb)) : JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
        coeffMap (IsLocalRing.residue ↥A) y) := by sorry
