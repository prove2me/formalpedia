-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_etale_chart_affineLine_of_isStrictSnd
-- name    : ModularCurve.XHDRModelAtP.exists_etale_chart_affineLine_of_isStrictSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/a4c03091-1da8-5d61-ae9b-faf6a3eac6ca
-- title:
--   Étale coordinate to A¹_A at a strict second-kind point
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under $\mathbb{Z}/M \to \mathbb{Z}/(M/p)$ is $1$; assume `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤` and let $\mathfrak{X}$ be a Deligne–Rapoport model `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ satisfy $A.\mathrm{subtype} \circ \rho =$ `algebraMap (R p) (AlgebraicClosure ℚ)`. The frame data are: a unit `pb` of $\mathbb{Z}/(M/p)$ whose underlying element is $p$; the map $\delta$ on places of `JHNeronObjectAtP.Fbar p M H hpM κ` given by acting with the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M/p) pb)` through `SemilinearAut.ofAlgAut`; a finset `SS` enumerating exactly the pairs in `ssNodePairsQExp κ (ΓN p M H hpM) p`; an $\overline{\mathbb{Q}}$-automorphism $\theta$ of `xHFunctionFieldBar M H`; an integral $\overline{\mathbb{Q}}$-algebra map $\alpha$ from `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` to `xHFunctionFieldBar M H` which is the identity on Laurent series, with $\theta \circ \alpha$ also integral; a place specialisation `Psp` and a prolongation datum `Rpd` for $\theta$; and the compatibility hypotheses `hwgen` ($\theta$-equivariance of the point–place correspondence of $\mathfrak{X}.\mathrm{Meta}$), `hTD` (type dichotomy), `hmodel` (the divisor and cusp laws), and `hcompat`, `hcompat'` (the two laws computing the place of a closed point of the fibre model in terms of `Psp.reduceFst`, `Psp.reduceSnd` and `qExpFrobeniusPlaceModL`), summarised here. Let $Q$ be a place of `xHFunctionFieldBar M H` that is strict of the second kind, i.e. `Psp.reduceFst α hα Q` equals the mod-$p$ Frobenius twist of `Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q` and the latter is not fixed by $\delta$. Let $u$ be an $A$-section of `toBase p (ΓM M H) hj` over $\operatorname{Spec}\rho$ whose associated $\overline{\mathbb{Q}}$-point is the one corresponding to $Q$ through $\mathfrak{X}.\mathrm{eeta}$, let $u_\kappa$ be a section of the fibre over $\kappa$ reducing $u$ modulo the maximal ideal of $A$, and let $P_0$ be a closed point of the fibre curve model $\mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho$ mapping, through $\mathfrak{X}.\mathrm{efib}$ followed by the component $\mathfrak{X}.\mathrm{comp}\,1$, to the closed point of $u_\kappa$, and with `placeOfPoint P0 = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q`; assume finally that this closed point of $u_\kappa$ does not lie in the image of the component $\mathfrak{X}.\mathrm{comp}\,0$. Writing $x_0$ for the image of the closed point of $u_\kappa$ in $XO =$ `pullback (toBase p (ΓM M H) hj) (Spec.map ρ)` under the base-change map `bcMap (ΓM M H) hj ρ (residue A)` (two further abbreviations, the base change $XQ$ of $\mathfrak{X}$ to $\overline{\mathbb{Q}}$ and the induced morphism $XQ \to XO$, are introduced but do not occur in the conclusion), the assertion is that there are an open $U$ of $XO$ containing $x_0$ and a morphism $f : U \to \operatorname{Spec} A[T]$ such that $f$ followed by $\operatorname{Spec}$ of $A \to A[T]$ is the inclusion $U \hookrightarrow XO$ followed by the structure morphism to $\operatorname{Spec} A$, such that $f$ is étale, and such that $f$ sends $x_0$ to the image of the closed point of $A$ under $\operatorname{Spec}$ of evaluation at $0$, i.e. to the origin of the special fibre of $\mathbb{A}^1_A$.
--
--   This is the existence of an étale coordinate on the Deligne–Rapoport model over $A$, vanishing at a $\kappa$-rational point of the special fibre that lies on only one of the two components: the point is in the smooth locus of the model over $\mathbb{Z}_{(p)}$, and a smooth morphism of relative dimension one admits, locally, an étale map to the affine line. It feeds the construction of a disc parameter and the resulting power-series reading of the local ring, [`ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictSnd`](thm.html#ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictSnd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_etale_chart_affineLine_of_isStrictSnd.lean

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

theorem ModularCurve.XHDRModelAtP.exists_etale_chart_affineLine_of_isStrictSnd
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
    :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl

    letI x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    ∃ (U : (XO (ΓM M H) hj ρ).Opens) (hxU : x₀ ∈ U) (f : (U : Scheme.{0}) ⟶ Spec (CommRingCat.of (Polynomial ↥A))),
      f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (Polynomial ↥A))) = U.ι ≫ pullback.snd _ _ ∧
      Etale f ∧
      f.base ⟨_, hxU⟩ = (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ↥A)))).base (IsLocalRing.closedPoint ↥A) := by sorry
