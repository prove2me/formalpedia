-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_residue_readA_eq_restrict_comp_zero_of_forall_isUnit_germ_iff_residue_ne_zero
-- name    : ModularCurve.XHDRModelAtP.residue_readA_eq_restrict_comp_zero_of_forall_isUnit_germ_iff_residue_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/8731b27f-70dc-5bc4-b509-29a12901af7d
-- title:
--   R₁-residue of a germ equals restriction along the zero component
-- statement:
--   Fix a prime $p$, a nonzero level $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under the map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial; assume $M/p \neq 0$ and that the $q$-expansion `jqModC ℚ` of $j$ lies in the level-$\mathrm{SL}(2,\mathbb{Z})$ function field, and let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj` package. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$ and with algebraically closed residue field $\kappa$ of characteristic $p$, and $\rho : R p \to A$ a ring homomorphism lifting $R p \to \overline{\mathbb{Q}}$. Let $\theta$ be an $\overline{\mathbb{Q}}$-algebra automorphism of $F :=$ `xHFunctionFieldBar M H`, let `Psp` be a `JHPlaceSpecialization` for $(p,M,H,A)$ and `Rpd` a prolongation datum for `Psp` and $\theta$, with first regular prolongation $R_1$ (a valuation subring of $F$ together with a surjective residue map onto the reduction field with kernel its maximal ideal). Write $X_{\overline{\mathbb{Q}}}$ for the base change of $\mathfrak{X}$ along $R p \to \overline{\mathbb{Q}}$, $\mathrm{pr}_A : X_{\overline{\mathbb{Q}}} \to$ `XO (ΓM M H) hj ρ` for the map induced by $A \hookrightarrow \overline{\mathbb{Q}}$, and $\mathrm{bc}_A$ for the base-change map from the fibre over $\kappa$ to `XO … ρ`. For an open $V$ of `XO … ρ` whose preimage in $\mathfrak{X}.\mathrm{Meta}.C$ (via $\mathrm{pr}_A$ and the isomorphism $\mathfrak{X}.\mathrm{eeta}$) contains the generic point, let $\mathrm{read}_A : \Gamma(\mathrm{XO}, V) \to F$ be the ring homomorphism obtained by pulling $g$ back along $\mathrm{pr}_A$ and $\mathfrak{X}.\mathrm{eeta}$, taking the germ at the generic point of $\mathfrak{X}.\mathrm{Meta}.C$, and transporting along $\mathfrak{X}.\mathrm{Meta}.\mathrm{ffEquiv}^{-1}$. Assume that $R_1$ dominates the local ring at the point `𝔛.ξinf A hA ρ hρ ρ (residue A) rfl`: for every such $V$ containing that point and every $g \in \Gamma(\mathrm{XO}, V)$, one has $\mathrm{read}_A g \in R_1$, and the germ of $g$ at that point is a unit if and only if its $R_1$-residue is nonzero. The conclusion is that for every such $V$, every $g$, and every proof that $\mathrm{read}_A g \in R_1$, the generic point of $(\mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$ lies in the preimage of $V$ under the composite $\mathfrak{X}.\mathrm{efib}$ followed by $\mathfrak{X}.\mathrm{comp}\,\cdots\,0$ followed by $\mathrm{bc}_A$, and the $R_1$-residue of $\mathrm{read}_A g$ equals the image of $g$ under that composite, taken as a germ at this generic point and transported along $(\mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).\mathrm{ffEquiv}^{-1}$.
--
--   This identifies the residue map of the first prolongation $R_1$, on sections of the $A$-model of $X_H(M)$ read at the generic point, with restriction to the component of the special fibre indexed $0$ through the fibre dictionary curve; informally, reduction modulo $p$ of a modular function is its restriction to that component. It is used by [`ModularCurve.XHDRModelAtP.readA_mem_integers_and_residue_eq_restrict_comp_of_mem`](thm.html#ModularCurve.XHDRModelAtP.readA_mem_integers_and_residue_eq_restrict_comp_of_mem), which removes the domination hypothesis, in the passage from the Deligne–Rapoport model to place specialisation at level $M$ with $p \,\|\, M$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_residue_readA_eq_restrict_comp_zero_of_forall_isUnit_germ_iff_residue_ne_zero.lean

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

theorem ModularCurve.XHDRModelAtP.residue_readA_eq_restrict_comp_zero_of_forall_isUnit_germ_iff_residue_ne_zero
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
    (∀ (V : (XO (ΓM M H) hj ρ).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V))
      (g : Γ(XO (ΓM M H) hj ρ, V)) (hi : 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ V),
      letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
        (𝔛.Meta).ffEquiv.symm.toRingHom.comp
          (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
            ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
      ∃ h : readA g ∈ Rpd.R₁.integers,
        (IsUnit ((XO (ΓM M H) hj ρ).presheaf.germ V _ hi g) ↔ Rpd.R₁.residue ⟨readA g, h⟩ ≠ 0)) →
    ∀ (V : (XO (ΓM M H) hj ρ).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V))
      (g : Γ(XO (ΓM M H) hj ρ, V)) (hi : 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ V),
    letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
          ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
    ∀ h : readA g ∈ Rpd.R₁.integers,
    letI := (𝔛.Mfib A hA ρ hρ).isIntegral
    ∃ hg₀ : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ V,
      Rpd.R₁.residue ⟨readA g, h⟩ =
        (𝔛.Mfib A hA ρ hρ).ffEquiv.symm
          (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ V) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₀)
            (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).app V).hom g)) := by sorry
