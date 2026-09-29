-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_reduceFst_eq_and_not_isStrict_of_section_closedPoint_eq_crossing_of_offDiag
-- name    : ModularCurve.XHDRModelAtP.reduceFst_eq_and_not_isStrict_of_section_closedPoint_eq_crossing_of_offDiag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/79a1d0ee-df76-5f77-901f-476f39e34818
-- title:
--   Section through a crossing: red₁ and non-strictness
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing the kernel of the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$; assume $j$ lies in the $q$-expansion function field of level $\mathrm{SL}_2(\mathbb{Z})$, and let $\mathfrak{X}$ be a model package `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over $R_p$. Further data: a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit in $A$, algebraically closed residue field $\kappa$ of characteristic $p$, and $\rho : R_p \to A$ compatible with $R_p \to \overline{\mathbb{Q}}$; a unit $pb$ of $\mathbb{Z}/(M/p)$ reducing to $p$, and the map $\delta$ on places of $\bar F =$ `qExpFunctionFieldC κ (ΓN p M H hpM)` given by the semilinear action of the diamond automorphism `diamondActionModL` at a $\Gamma_0(M/p)$-lift of $pb$; a finite set $SS$ whose members are exactly the pairs $(\mathrm{Frob}_p(v), v)$ with $v$ supersingular (the set `ssNodePairsQExp`); a $\overline{\mathbb{Q}}$-automorphism $\theta$ of $\bar F_M =$ `xHFunctionFieldBar M H` and an integral $\overline{\mathbb{Q}}$-embedding $\alpha$ of `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` into $\bar F_M$ with $\theta \circ \alpha$ also integral and $\alpha$ the identity on $q$-expansions; a place specialisation datum $\mathrm{Psp}$ and a prolongation datum $\mathrm{Rpd}$ for $\theta$, satisfying the type dichotomy for $(\alpha, \theta\alpha, \delta)$ and the model conditions `IsModel`; the hypothesis `hwgen` that $\theta$ implements the second projection $\mathfrak{X}.w$ on $\overline{\mathbb{Q}}$-points, and the two compatibility hypotheses `hcompat`, `hcompat'` identifying, for each component $i \in \{0,1\}$ of the special fibre, the place of a closed point of the fibre curve lying under a $\kappa$-point with $\mathrm{red}_1$, resp. $\mathrm{red}_2$, of the place of the corresponding generic point, and conversely up to Frobenius; and a discrete valuation ring $O$ with uniformiser $p$, maps $\rho_O : R_p \to O$, $\mathrm{to}\kappa : O \to \kappa$ surjective, $j_O : O \to \overline{\mathbb{Q}}$ and $\iota_A : O \to A$ all compatible (hypotheses summarised here). Let $n$ be a point of the fibre product of the two components of the special fibre whose pair of places $(\mathrm{Frob}_p(v_n), v_n)$ equals a given element $nd$ of $SS$, let $W$ be a place of $\bar F_M$ over $\overline{\mathbb{Q}}$, and let $s_A : \operatorname{Spec} A \to \mathfrak{X} \times_{R_p} \operatorname{Spec} O$ be a section over $\iota_A$ whose base change to $\overline{\mathbb{Q}}$ is the point corresponding to $W$ under `Meta.pointEquivPlace` and whose closed point is the image of the crossing $n$. Then $\mathrm{Psp}.\mathrm{reduceFst}\,\alpha\,W = \mathrm{Psp}.\mathrm{sp}(W|_\alpha)$ equals the first component of $nd$, and neither `IsStrictFst` nor `IsStrictSnd` holds for $W$ with respect to $(\alpha, \theta\alpha, \delta)$, i.e. $W$ is strict on neither sheet.
--
--   This is the forward half of the dictionary between crossings of the special fibre of the Deligne–Rapoport model of $X_H(M)$ at a prime $p$ exactly dividing $M$ and places of the geometric function field that are non-strict, as used in the level-lowering argument: an $A$-valued section whose closed point is a crossing reads off that crossing's node pair through the first reduction map, and supersingular places being fixed by the diamond action $\delta$ forces non-strictness on both sheets. It is cited by [`ModularCurve.XHDRModelAtP.exists_section_through_crossing_iff_reduceFst_eq_and_not_isStrict_of_offDiag_of_surjective`](thm.html#ModularCurve.XHDRModelAtP.exists_section_through_crossing_iff_reduceFst_eq_and_not_isStrict_of_offDiag_of_surjective), which packages the two directions into an equivalence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_reduceFst_eq_and_not_isStrict_of_section_closedPoint_eq_crossing_of_offDiag.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.reduceFst_eq_and_not_isStrict_of_section_closedPoint_eq_crossing_of_offDiag
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
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)
    (hsurj : Function.Surjective toκ)
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (nd : ↥SS)
    (hn : (𝔛.placeOn0 A hA ρ hρ n, 𝔛.placeOn1 A hA ρ hρ n) = (nd : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))

    (sA : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj ρO)
    (hsA₁ : sA ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA))
    (hsA₂ : barPt A ≫ sA = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫
      (pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
          (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)) (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO]) :
          pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρO))
    (hsA₃ : sA.base (IsLocalRing.closedPoint ↥A) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n) :
    Psp.reduceFst α hα W = nd.1.1 ∧
        ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧
        ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W := by sorry
