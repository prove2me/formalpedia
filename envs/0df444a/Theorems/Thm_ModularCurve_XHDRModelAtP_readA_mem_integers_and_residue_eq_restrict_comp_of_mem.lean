-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_readA_mem_integers_and_residue_eq_restrict_comp_of_mem
-- name    : ModularCurve.XHDRModelAtP.readA_mem_integers_and_residue_eq_restrict_comp_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/e7b07ed9-2b16-534e-a2f9-54ae4e73575b
-- title:
--   Readings of sections at the two components: integrality and residue
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, with $M/p \neq 0$, and assume $j$ lies in the $q$-expansion function field `qExpFunctionFieldC ℚ ⊤`; let $\mathfrak{X}$ be an integral model datum `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over $R_p$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ be a ring homomorphism compatible with $R_p \to \overline{\mathbb{Q}}$. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $F :=$ `xHFunctionFieldBar M H`, let `Psp` be a place specialisation `JHPlaceSpecialization p M H hpM A`, and let `Rpd` be a prolongation datum for `Psp` and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F$ with values in the special-fibre field, $R_1$ computing coefficientwise reduction of Laurent series and $R_2$ obtained from $R_1$ by precomposing with $\theta$. Assume further that $\theta$ implements $\mathfrak{X}.w$ on $\overline{\mathbb{Q}}$-points: whenever two $\overline{\mathbb{Q}}$-points $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base satisfy $y'$ followed by `eeta`, `pullback.fst` and $\mathfrak{X}.w$ equal to $y$ followed by `eeta` and `pullback.fst`, the associated places satisfy `pointEquivPlace y' = SemilinearAut.ofAlgAut θ • pointEquivPlace y`. Write $X_{\overline{\mathbb{Q}}}$ for the base change of the model to $\overline{\mathbb{Q}}$, `prA` for the induced map to the base change $X_A$ along $A \hookrightarrow \overline{\mathbb{Q}}$, and `bcA` for the map from the fibre over the residue field of $A$ to $X_A$. Then for every open $V \subseteq X_A$ whose preimage under `prA` and then `eeta` contains the generic point of $\mathfrak{X}.\mathrm{Meta}.C$, and every $g \in \Gamma(X_A, V)$, with `readA g` the element of $F$ obtained by restricting $g$ along `prA` and `eeta`, taking the germ at that generic point and transporting along `ffEquiv.symm`: if the point $\xi_\infty$ of the special fibre lies in $V$ then `readA g` lies in the valuation subring $R_1$.`integers`, its $R_1$-residue equals the corresponding germ at the generic point of the special-fibre curve model $\mathfrak{X}.\mathrm{Mfib}$ of the pullback of $g$ along `efib`, the zeroth component map and `bcA` (read through that model's `ffEquiv.symm`), and if the germ of $g$ at $\xi_\infty$ is a unit then this residue is non-zero; symmetrically, if $\xi_0$ lies in $V$ then `readA g` lies in $R_2$.`integers` with residue given by the first component map, non-zero when the germ of $g$ at $\xi_0$ is a unit.
--
--   This is the $q$-expansion dictionary for the Deligne–Rapoport model in its valuation-ring form: a section regular at the generic point of either component of the geometric special fibre is integral for the corresponding prolongation of $A$, and its residue is its restriction to that component. It is used downstream to produce local parameters and power-series readings of stalks at the crossing points, and to exhibit sections that are units at a crossing with prescribed order along a component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_readA_mem_integers_and_residue_eq_restrict_comp_of_mem.lean

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

theorem ModularCurve.XHDRModelAtP.readA_mem_integers_and_residue_eq_restrict_comp_of_mem
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
    ∀ (V : (XO (ΓM M H) hj ρ).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V))
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
        (IsUnit ((XO (ΓM M H) hj ρ).presheaf.germ V _ hi g) → Rpd.R₁.residue ⟨readA g, h₁⟩ ≠ 0)) ∧

    (∀ h0 : 𝔛.ξzero A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ V,
      ∃ h₂ : readA g ∈ Rpd.R₂.integers,
        (letI := (𝔛.Mfib A hA ρ hρ).isIntegral
         ∃ hg₁ : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA) ⁻¹ᵁ V,
          Rpd.R₂.residue ⟨readA g, h₂⟩ =
            (𝔛.Mfib A hA ρ hρ).ffEquiv.symm
              (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA) ⁻¹ᵁ V) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₁)
                (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA).app V).hom g))) ∧
        (IsUnit ((XO (ΓM M H) hj ρ).presheaf.germ V _ h0 g) → Rpd.R₂.residue ⟨readA g, h₂⟩ ≠ 0)) := by sorry
