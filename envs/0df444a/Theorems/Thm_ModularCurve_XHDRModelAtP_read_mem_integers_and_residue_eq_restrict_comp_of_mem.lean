-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_read_mem_integers_and_residue_eq_restrict_comp_of_mem
-- name    : ModularCurve.XHDRModelAtP.read_mem_integers_and_residue_eq_restrict_comp_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/8fb0a868-b371-55c7-8886-427c33915dd8
-- title:
--   Integrality and residues of a section at both special-fibre components
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$, $p^{2} \nmid M$, a subgroup $H \le (\mathbb Z/M)^{\times}$ containing every unit whose image in $(\mathbb Z/(M/p))^{\times}$ is $1$, and the hypothesis `hj` that the $q$-expansion `jqModC ℚ` lies in the full-level field `qExpFunctionFieldC ℚ ⊤`; let `𝔛 : XHDRModelAtP p M H hpM hj` be a model package for $X_H(M)$ over `R p`. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ for which $p$ is a nonunit, with residue field $\kappa$ algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ satisfy $A.\mathrm{subtype} \circ \rho =$ the structure map $R_p \to \overline{\mathbb Q}$. Let $O$ be a commutative ring equipped with $\rho_O : R_p \to O$, $\mathrm{to}\kappa : O \to \kappa$, $j_O : O \to \overline{\mathbb Q}$ and $\iota_A : O \to A$ such that $\mathrm{to}\kappa \circ \rho_O$ is the residue map composed with $\rho$, $j_O \circ \rho_O$ is the structure map, $A.\mathrm{subtype} \circ \iota_A = j_O$ and the residue map composed with $\iota_A$ is $\mathrm{to}\kappa$. Let $\theta$ be an $\overline{\mathbb Q}$-algebra automorphism of the geometric function field `xHFunctionFieldBar M H`, let `Psp` be a `JHPlaceSpecialization` for $p, M, H, A$ and `Rpd` a `ProlongationDatum` for `Psp` and $\theta$; thus `Rpd.R₁` and `Rpd.R₂` are regular prolongations of $A$ to `xHFunctionFieldBar M H` with residues in the special-fibre function field `Fbar`, tied by $f \in$ `R₂.integers` $\iff \theta f \in$ `R₁.integers` and `R₂.residue f = R₁.residue (θ f)`. Assume `hwgen`: for any two $\overline{\mathbb Q}$-points $y, y'$ of `𝔛.Meta.C` over its base (morphisms $q$ with $q$ followed by `𝔛.Meta.toBase` the identity), if the image of $y'$ under `𝔛.eeta` and `pullback.fst`, followed by `𝔛.w.hom`, equals the corresponding image of $y$, then the place attached to $y'$ by `𝔛.Meta.pointEquivPlace` is the translate of that of $y$ by the image of $\theta$ in `SemilinearAut`. Write $X_{\overline{\mathbb Q}}$ for the base change of `toBase p (ΓM M H) hj` along $R_p \to \overline{\mathbb Q}$ and `prJ` for the induced morphism $X_{\overline{\mathbb Q}} \to$ `XO (ΓM M H) hj ρO` coming from $j_O$. Then for every open $V$ of `XO (ΓM M H) hj ρO` such that the generic point of `𝔛.Meta.C` lies in the `𝔛.eeta`-preimage of the `prJ`-preimage of $V$, and every $g \in \Gamma(V)$, let `readV g` be the germ of the pull-back of $g$ along `prJ` and `𝔛.eeta` at that generic point, transported by `𝔛.Meta.ffEquiv.symm` into `xHFunctionFieldBar M H`. The assertion is twofold. First, if the point `𝔛.ξinf A hA ρ hρ ρO toκ htoκ` lies in $V$, then `readV g` lies in `Rpd.R₁.integers`, the generic point of the curve `(𝔛.Mfib A hA ρ hρ).C` lies in the preimage of $V$ under `𝔛.efib` followed by `𝔛.comp … 0` followed by `bcMap (ΓM M H) hj ρO toκ htoκ`, its `R₁`-residue equals the germ there of the pull-back of $g$ along that composite, read through `(𝔛.Mfib A hA ρ hρ).ffEquiv.symm`, and this residue is nonzero whenever the germ of $g$ at `𝔛.ξinf …` is a unit. Second, the same statement with `𝔛.ξzero A hA ρ hρ ρO toκ htoκ`, `Rpd.R₂` and `𝔛.comp … 1` in place of `𝔛.ξinf …`, `Rpd.R₁` and `𝔛.comp … 0`.
--
--   This is the element-level dictionary between sections of the Deligne–Rapoport-type model over an arbitrary `R p`-algebra $O$ and the two regular prolongations of the valuation $A$ attached to the two components of the geometric special fibre: a section regular at a component's generic point is integral there, and its residue is its restriction to that component, read in the special-fibre function field. It is obtained from the corresponding statement over $A$ itself, `readA_mem_integers_and_residue_eq_restrict_comp_of_mem`, and is used in the stalk-level unit and width statements for the crossing annuli at supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_read_mem_integers_and_residue_eq_restrict_comp_of_mem.lean

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

theorem ModularCurve.XHDRModelAtP.read_mem_integers_and_residue_eq_restrict_comp_of_mem
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] (ρO : R p →+* O)
    (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
    ∀ (V : (XO (ΓM M H) hj ρO).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ V))
      (g : Γ(XO (ΓM M H) hj ρO, V)),
    letI readV : Γ(XO (ΓM M H) hj ρO, V) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
          ((𝔛.eeta.app (prJ ⁻¹ᵁ V)).hom.comp (prJ.app V).hom))

    (∀ hi : 𝔛.ξinf A hA ρ hρ ρO toκ htoκ ∈ V,
      ∃ h₁ : readV g ∈ Rpd.R₁.integers,
        (letI := (𝔛.Mfib A hA ρ hρ).isIntegral
         ∃ hg₀ : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ) ⁻¹ᵁ V,
          Rpd.R₁.residue ⟨readV g, h₁⟩ =
            (𝔛.Mfib A hA ρ hρ).ffEquiv.symm
              (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ) ⁻¹ᵁ V) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₀)
                (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).app V).hom g))) ∧
        (IsUnit ((XO (ΓM M H) hj ρO).presheaf.germ V _ hi g) → Rpd.R₁.residue ⟨readV g, h₁⟩ ≠ 0)) ∧

    (∀ h0 : 𝔛.ξzero A hA ρ hρ ρO toκ htoκ ∈ V,
      ∃ h₂ : readV g ∈ Rpd.R₂.integers,
        (letI := (𝔛.Mfib A hA ρ hρ).isIntegral
         ∃ hg₁ : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ) ⁻¹ᵁ V,
          Rpd.R₂.residue ⟨readV g, h₂⟩ =
            (𝔛.Mfib A hA ρ hρ).ffEquiv.symm
              (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ) ⁻¹ᵁ V) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₁)
                (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).app V).hom g))) ∧
        (IsUnit ((XO (ΓM M H) hj ρO).presheaf.germ V _ h0 g) → Rpd.R₂.residue ⟨readV g, h₂⟩ ≠ 0)) := by sorry
