-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_forall_readA_mem_integers_snd_of_forall_readA_mem_integers_fst
-- name    : ModularCurve.XHDRModelAtP.forall_readA_mem_integers_snd_of_forall_readA_mem_integers_fst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/74fbd85e-56be-5cbf-a007-c2726bc58470
-- title:
--   Transporting the residue dictionary from ξ_∞ to ξ₀
-- statement:
--   Fix a prime $p$ and $M \ne 0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^\times$, with $M/p \ne 0$, and assume $j$ lies in the $q$-expansion function field `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj` package, $A$ a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ and with algebraically closed residue field of characteristic $p$, and $\rho : R_p \to A$ a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Let $\theta$ be an $\overline{\mathbb{Q}}$-algebra automorphism of `xHFunctionFieldBar M H`, let `Psp` be a `JHPlaceSpecialization` for $(p,M,H,A)$ and `Rpd` a `ProlongationDatum` for `Psp` and $\theta$, with regular prolongations $R_1$, $R_2$ satisfying $f \in R_2$ iff $\theta f \in R_1$ and $\mathrm{res}_{R_2}(f) = \mathrm{res}_{R_1}(\theta f)$. Assume further `hwgen`: whenever two $\overline{\mathbb{Q}}$-points $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base satisfy that $y'$ followed by $\mathfrak{X}.\mathrm{eeta}$, the first pullback projection and the isomorphism $\mathfrak{X}.w$ equals $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first projection, then the place attached to $y'$ by `Meta.pointEquivPlace` is the translate of the place attached to $y$ by the semilinear automorphism $(\theta, 1)$. Write $X_{\overline{\mathbb{Q}}}$ for the base change of the integral model along $R_p \to \overline{\mathbb{Q}}$, $\mathrm{pr}_A : X_{\overline{\mathbb{Q}}} \to XO(\Gamma_M, \rho)$ for the map induced by $A \hookrightarrow \overline{\mathbb{Q}}$, and $\mathrm{bc}_A$ for the comparison map from the fibre over the residue field of $A$. For an open $V$ of $XO(\Gamma_M,\rho)$ whose preimage under $\mathrm{pr}_A$ and then $\mathfrak{X}.\mathrm{eeta}$ contains the generic point of $\mathfrak{X}.\mathrm{Meta}.C$, let $\mathrm{read}_A : \Gamma(XO, V) \to$ `xHFunctionFieldBar M H` be restriction along $\mathrm{pr}_A$, then along $\mathfrak{X}.\mathrm{eeta}$, then the germ at that generic point, transported by $\mathfrak{X}.\mathrm{Meta}.\mathrm{ffEquiv}^{-1}$. The assertion is: if for all such $V$ and all $g \in \Gamma(XO, V)$ with $\mathfrak{X}.\xi_{\inf} \in V$ one has $\mathrm{read}_A g \in R_1$, the $R_1$-residue of $\mathrm{read}_A g$ equals the germ at the generic point of $\mathfrak{X}.\mathrm{Mfib}.C$ of the pullback of $g$ along $\mathfrak{X}.\mathrm{efib}$ followed by the $0$-th component map and $\mathrm{bc}_A$ (transported by $\mathfrak{X}.\mathrm{Mfib}.\mathrm{ffEquiv}^{-1}$), and this residue is non-zero whenever the germ of $g$ at $\mathfrak{X}.\xi_{\inf}$ is a unit, then the same three conclusions hold for all $V$ and $g$ with $\mathfrak{X}.\xi_{\mathrm{zero}} \in V$, with $R_1$ replaced by $R_2$ and the $0$-th component map by the $1$-st.
--
--   This is the transport, along the Atkin–Lehner isomorphism $w$ of the Deligne–Rapoport-style integral model, of the dictionary between sections of the model over $A$ and elements of the regular prolongation: the statement at the generic point $\xi_0$ of one component of the special fibre is deduced from the statement at the generic point $\xi_\infty$ of the other, using that $w$ acts on places as the automorphism $\theta$ and that $R_2$ is the $\theta$-pullback of $R_1$. It feeds the combined reading lemma [`ModularCurve.XHDRModelAtP.readA_mem_integers_and_residue_eq_restrict_comp_of_mem`](thm.html#ModularCurve.XHDRModelAtP.readA_mem_integers_and_residue_eq_restrict_comp_of_mem), which treats both components at once.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_forall_readA_mem_integers_snd_of_forall_readA_mem_integers_fst.lean

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

set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.forall_readA_mem_integers_snd_of_forall_readA_mem_integers_fst
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
    (∀ (V : (XO (ΓM M H) hj ρ).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V))
      (g : Γ(XO (ΓM M H) hj ρ, V)),
      letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
        (𝔛.Meta).ffEquiv.symm.toRingHom.comp
          (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
            ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
      (∀ hi : 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ V,
        ∃ h₁ : readA g ∈ Rpd.R₁.integers,
          (letI := (𝔛.Mfib A hA ρ hρ).isIntegral
           ∃ hg₀ : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ V,
            Rpd.R₁.residue ⟨readA g, h₁⟩ =
              (𝔛.Mfib A hA ρ hρ).ffEquiv.symm
                (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ V) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₀)
                  (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).app V).hom g))) ∧
          (IsUnit ((XO (ΓM M H) hj ρ).presheaf.germ V _ hi g) → Rpd.R₁.residue ⟨readA g, h₁⟩ ≠ 0))) →
    ∀ (V : (XO (ΓM M H) hj ρ).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V))
      (g : Γ(XO (ΓM M H) hj ρ, V)),
    letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
          ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
    (∀ h0 : 𝔛.ξzero A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ V,
      ∃ h₂ : readA g ∈ Rpd.R₂.integers,
        (letI := (𝔛.Mfib A hA ρ hρ).isIntegral
         ∃ hg₁ : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA) ⁻¹ᵁ V,
          Rpd.R₂.residue ⟨readA g, h₂⟩ =
            (𝔛.Mfib A hA ρ hρ).ffEquiv.symm
              (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA) ⁻¹ᵁ V) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₁)
                (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA).app V).hom g))) ∧
        (IsUnit ((XO (ΓM M H) hj ρ).presheaf.germ V _ h0 g) → Rpd.R₂.residue ⟨readA g, h₂⟩ ≠ 0)) := by sorry
