-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_section_eq_of_specMap_residue_comp_eq_of_comp_etale_chart_eq_of_isStrictSnd
-- name    : ModularCurve.XHDRModelAtP.section_eq_of_specMap_residue_comp_eq_of_comp_etale_chart_eq_of_isStrictSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/58b5338b-ca8d-550c-b537-f82fed8b0114
-- title:
--   Uniqueness of A-sections in an étale chart
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb Z/M)^\times$ containing the kernel of the reduction $(\mathbb Z/M)^\times \to (\mathbb Z/(M/p))^\times$, the hypothesis that the $q$-expansion of $j$, `jqModC ℚ`, lies in the full-level field `qExpFunctionFieldC ℚ ⊤`, and a Deligne–Rapoport datum $\mathfrak X$ : `XHDRModelAtP p M H hpM hj`. Fix a valuation subring $A \subset \overline{\mathbb Q}$ with $p$ a nonunit of $A$, with algebraically closed residue field $\kappa$ of characteristic $p$, and a ring map $\rho : R_p \to A$ compatible with $R_p \to \overline{\mathbb Q}$. Further data: a unit $pb$ of $\mathbb Z/(M/p)$ represented by $p$; the self-map $\delta$ of places of `Fbar p M H hpM κ` given by the diamond automorphism `diamondActionModL` at [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36); a finset $SS$ whose members are exactly the pairs in `ssNodePairsQExp κ (ΓN p M H hpM) p`; an automorphism $\theta$ of `xHFunctionFieldBar M H` over $\overline{\mathbb Q}$ and an integral algebra map $\alpha$ from level $M/p$ into it with $\alpha$ followed by $\theta$ integral and $\alpha$ the identity on Laurent series; a place specialisation $Psp$ and a prolongation datum $Rpd$ for $\theta$; and the structural hypotheses (Galois behaviour of places via `𝔛.w`, the type dichotomy, `Rpd.IsModel`, and the two compatibility hypotheses `hcompat`, `hcompat'` identifying places of closed points of the fibre model `𝔛.Mfib A hA ρ hρ` with `Psp.reduceFst`/`Psp.reduceSnd` and their Frobenius twists), summarised here. Finally fix a place $Q$ of `xHFunctionFieldBar M H` satisfying `Psp.IsStrictSnd`, that is $\mathrm{red}_1(Q)$ equals the Frobenius restriction of $\mathrm{red}_2(Q)$ while $\mathrm{red}_2(Q)$ fails the predicate `Fixed` for $\delta$; an $A$-section $u$ of `toBase p (ΓM M H) hj` whose $\overline{\mathbb Q}$-point is the one attached to $Q$, its reduction $u_\kappa$ to the special fibre, and a closed point $P_0$ of `(𝔛.Mfib A hA ρ hρ).C` lying over the special point of $u_\kappa$ on the component indexed $1$, with place $\mathrm{red}_2(Q)$ and with that special point outside the image of the component indexed $0$. Given an open $U$ of the base change `XO (ΓM M H) hj ρ` containing the image of this special point and an étale $A$-morphism $f : U \to \operatorname{Spec} A[T]$ sending that point to the origin of the special fibre, the conclusion asserts: any two sections $s, s' : \operatorname{Spec} A \to U$ over $A$ which induce the same $\kappa$-point and satisfy $f \circ s = f \circ s'$ are equal. Abbreviations for the base change to $\overline{\mathbb Q}$, its projection to `XO`, the reduction map and the point $x_0$ are introduced but do not enter the conclusion, which concerns only the étale chart $(U, f)$ over $A$.
--
--   This is the rigidity of sections along an étale morphism, in the shape needed on the Deligne–Rapoport model of $X_H(M)$ at a level exactly divisible by $p$: an $A$-valued section landing in an étale chart is determined by its reduction modulo the maximal ideal of $A$ together with the value of the chart coordinate. It is used to obtain injectivity of the reading of the disc parameter on a residue disc around a smooth point of the special fibre, in [`ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictSnd`](thm.html#ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictSnd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_section_eq_of_specMap_residue_comp_eq_of_comp_etale_chart_eq_of_isStrictSnd.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.section_eq_of_specMap_residue_comp_eq_of_comp_etale_chart_eq_of_isStrictSnd
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0Q : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q)
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 0).base)

    (U : (XO (ΓM M H) hj ρ).Opens) (hxU : (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈ U)
    (f : (U : Scheme.{0}) ⟶ Spec (CommRingCat.of (Polynomial ↥A)))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (Polynomial ↥A))) = U.ι ≫ pullback.snd _ _)
    (het : Etale f)
    (hpt : f.base ⟨_, hxU⟩ = (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ↥A)))).base (IsLocalRing.closedPoint ↥A))
    :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl

    letI x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    ∀ s s' : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}),
      s ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ → s' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ →

      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s' →
      s ≫ f = s' ≫ f → s = s' := by sorry
