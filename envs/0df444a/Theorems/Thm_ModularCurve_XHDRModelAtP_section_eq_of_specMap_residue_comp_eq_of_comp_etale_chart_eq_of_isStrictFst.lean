-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_section_eq_of_specMap_residue_comp_eq_of_comp_etale_chart_eq_of_isStrictFst
-- name    : ModularCurve.XHDRModelAtP.section_eq_of_specMap_residue_comp_eq_of_comp_etale_chart_eq_of_isStrictFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/d2cca21c-7630-58df-84fe-5a679d363db9
-- title:
--   Uniqueness of A-sections with a common étale coordinate
-- statement:
--   Fix a prime $p$ and $M>0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb Z/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb Z/(M/p))^\times$, and assume $M/p \neq 0$ and that `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak X$ be an `XHDRModelAtP p M H hpM hj`, an integral model datum for $X_H(M)$ over $R\,p$ equipped with its geometric curve model $\mathfrak X.\mathrm{Meta}$ of the function field $FM =$ `xHFunctionFieldBar M H`. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$, residue field $\kappa$ algebraically closed of characteristic $p$, and $\rho : R\,p \to A$ a ring map whose composite with the inclusion $A \hookrightarrow \overline{\mathbb Q}$ is the structural map. Further data: a unit $pb$ of $\mathbb Z/(M/p)$ with underlying element $p$; the map $\delta$ on places of $Fbar$ given by the action of the diamond automorphism attached to a $\Gamma_0(M/p)$-lift of $pb$; a finset $SS$ whose members are exactly the pairs in `ssNodePairsQExp`, i.e. pairs $(w_1,w_2)$ with $w_2$ supersingular and $w_1$ its mod-$p$ Frobenius place; an automorphism $\theta$ of $FM$ over $\overline{\mathbb Q}$; an integral algebra map $\alpha$ from `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` to $FM$ with $\alpha$ followed by $\theta$ also integral; a place specialisation $Psp$ and a prolongation datum $Rpd$ for $\theta$; and hypotheses $hwgen$, $h\alpha\_coe$, $hTD$, $hmodel$, $hcompat$, $hcompat'$ relating geometric points, places, their reductions along $\alpha$ and $\theta \circ \alpha$, Frobenius and the two components of the special fibre (summarised here). Let $Q$ be a place of $FM$ that is strict of the first kind, i.e. $\delta$ of the Frobenius of $Psp.\mathrm{reduceFst}\,\alpha\,Q$ equals $Psp.\mathrm{reduceSnd}\,(\theta \circ \alpha)\,\delta\,Q$ while $Psp.\mathrm{reduceFst}\,\alpha\,Q$ is not $\delta$-fixed, and let $u$ be a section over $\operatorname{Spec}\rho$ of the structure morphism, $u_\kappa$ a section of the fibre over $\kappa$ compatible with $u$, and $P_0$ a closed point of the fibre curve model lying over the closed point of $u_\kappa$, with place $Psp.\mathrm{reduceFst}\,\alpha\,Q$ and with that special point outside the image of the second component. Notation is fixed for the base change of $X$ to $\overline{\mathbb Q}$, the induced map to $XO = X \times_{\operatorname{Spec} R\,p} \operatorname{Spec} A$, the base-change map from the $\kappa$-fibre, and the resulting point $x_0 \in XO$. Finally let $U \subseteq XO$ be an open containing $x_0$ and $f : U \to \operatorname{Spec} A[T]$ an étale morphism over $\operatorname{Spec} A$ (that is, $f$ followed by $\operatorname{Spec}$ of $A \to A[T]$ equals the inclusion of $U$ followed by the projection to $\operatorname{Spec} A$) sending $x_0$ to the image of the closed point of $A$ under evaluation $T \mapsto 0$. The conclusion is that any two morphisms $s, s' : \operatorname{Spec} A \to U$ that are sections of the projection to $\operatorname{Spec} A$, agree after composing with $\operatorname{Spec}$ of the residue map $A \to \kappa$, and satisfy $s$ followed by $f$ equals $s'$ followed by $f$, are equal.
--
--   This is the rigidity of lifts along an étale morphism in the form needed on the Deligne–Rapoport model: an $A$-valued section of an étale chart is determined by its reduction modulo the maximal ideal of $A$ together with its étale coordinate. It is used in the construction of a disc parameter at a smooth special point of the first kind, by [`ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst`](thm.html#ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_section_eq_of_specMap_residue_comp_eq_of_comp_etale_chart_eq_of_isStrictFst.lean

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

theorem ModularCurve.XHDRModelAtP.section_eq_of_specMap_residue_comp_eq_of_comp_etale_chart_eq_of_isStrictFst
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

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0Q : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceFst α hα Q)
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 1).base)

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
