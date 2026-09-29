-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_mem_range_comp_and_not_crossing_of_isStrict_of_placeSpecializationKit_offDiag
-- name    : ModularCurve.XHDRModelAtP.mem_range_comp_and_not_crossing_of_isStrict_of_placeSpecializationKit_offDiag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/311751f5-3f5e-53e6-aaca-6c55cd7cc388
-- title:
--   Strict places land on their own component, off the crossings
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$, $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^\times$, and $hj$ asserting that the $q$-expansion `jqModC ℚ` lies in the full-level function field. Let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`, so in particular a proper flat normal integral model of $X_H(M)$ over $R p$ together with a curve model $\mathfrak{X}.\mathrm{Meta}$ of $F_M =$ `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$, identified by `eeta` with the base change, and its fibre data `Mfib`, `efib`, `comp 0`, `comp 1`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit, residue field $\kappa$ algebraically closed of characteristic $p$, and $\rho : R p \to A$ inducing the structural map to $\overline{\mathbb{Q}}$. Let $\theta$ be a $\overline{\mathbb{Q}}$-automorphism of $F_M$, $\alpha : F_{M/p} \to F_M$ an integral $\overline{\mathbb{Q}}$-algebra map which is the identity on underlying Laurent series, with $\theta \circ \alpha$ also integral; let $pb$ be a unit of $\mathbb{Z}/(M/p)$ represented by $p$, and $\delta$ the action on places of $F_b =$ `qExpFunctionFieldC κ (ΓN p M H hpM)` of the semilinear automorphism attached to the diamond operator `diamondActionModL` at the lift [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36). Let $Psp$ be a `JHPlaceSpecialization` with specialization map $\mathrm{sp}$, $Rpd$ a `ProlongationDatum` for $Psp$ and $\theta$, and assume: the type dichotomy for $(\alpha, \theta\circ\alpha, \delta)$, the model and fixed-order laws `IsModel` and `OrderLawFixed` for $Rpd$, and two families of compatibility hypotheses (`hcompat`, `hcompat'`) which, for $i \in \{0,1\}$, each $\overline{\mathbb{Q}}$-point $y$ of $\mathfrak{X}.\mathrm{Meta}.C$, each $A$-section $u$ over $\operatorname{Spec}\rho$ restricting to $y$, each compatible $\kappa$-point $u\kappa$ of the fibre, and each closed point $P_0$ of the fibre curve lying over the closed point of $u\kappa$ through `comp i`, read the place of $P_0$ as $\mathrm{sp}$ of the restriction of the place of $y$ along $\alpha$ (for $i=0$) respectively $\delta\,\mathrm{sp}$ of its restriction along $\theta\circ\alpha$ (for $i=1$), and read the other component off-diagonally through the mod-$p$ Frobenius `qExpFrobeniusPlaceModL`. The conclusion: for every place $V$ of $F_M$ over $\overline{\mathbb{Q}}$, every $A$-section $s$ of the model over $\operatorname{Spec}\rho$ whose generic restriction is the $\overline{\mathbb{Q}}$-point corresponding to $V$ under `pointEquivPlace`, and every $\kappa$-point $y\kappa$ of the fibre reducing $s$ and splitting the projection, if $V$ satisfies `IsStrictFst` (that is, $\delta$ of the Frobenius of $\mathrm{sp}(V|_\alpha)$ equals $\delta\,\mathrm{sp}(V|_{\theta\alpha})$ and $\mathrm{sp}(V|_\alpha)$ is not `Fixed` for $\delta$) then the image of the closed point under $y\kappa$ lies in the range of `comp 0` and not in the ranges of both `comp 0` and `comp 1`; and if $V$ satisfies `IsStrictSnd` (that is, $\mathrm{sp}(V|_\alpha)$ equals the Frobenius of $\delta\,\mathrm{sp}(V|_{\theta\alpha})$, the latter not `Fixed` for $\delta$) then it lies in the range of `comp 1`, again not in both.
--
--   This is the component-location statement for the Deligne–Rapoport special fibre of $X_H(M)$ at a prime exactly dividing the level: a place of the function field that is strict of the first (respectively second) kind specializes into the component indexed by $0$ (respectively $1$) and avoids the crossing locus where the two components meet. It is used in the construction of points on the Néron object at $p$, by [`ModularCurve.JHNeronObjectAtP.extendsToPlace_pts_of_forall_dvd_ord_residue_of_abelJacobiPin_offDiag_of_wgen`](thm.html#ModularCurve.JHNeronObjectAtP.extendsToPlace_pts_of_forall_dvd_ord_residue_of_abelJacobiPin_offDiag_of_wgen) and [`ModularCurve.JHNeronObjectAtP.extendsToPlace_pts_of_isGoodClass_of_abelJacobiPin_offDiag`](thm.html#ModularCurve.JHNeronObjectAtP.extendsToPlace_pts_of_isGoodClass_of_abelJacobiPin_offDiag).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_mem_range_comp_and_not_crossing_of_isStrict_of_placeSpecializationKit_offDiag.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.mem_range_comp_and_not_crossing_of_isStrict_of_placeSpecializationKit_offDiag
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
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
    :
    ∀ (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
      (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 =
        ((𝔛.Meta.pointEquivPlace).symm V).1 ≫ 𝔛.eeta ≫
          pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
      (yκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : yκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1) (_ : yκ ≫ pullback.snd _ _ = 𝟙 _),
      (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V →
        yκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧
        ¬ (yκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧
            yκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 1).base)) ∧
      (Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V →
        yκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 1).base ∧
        ¬ (yκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧
            yκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 1).base)) := by sorry
