-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_section_comp_zero_placeOfPoint_eq_reduceFst_of_isStrictFst
-- name    : ModularCurve.XHDRModelAtP.exists_section_comp_zero_placeOfPoint_eq_reduceFst_of_isStrictFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/9ceca960-e9dc-5297-a757-a3ac37a82472
-- title:
--   Sections realising strict places of the first kind
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that maps to $1$ under reduction to $(\mathbb{Z}/(M/p))^\times$; assume $j$ lies in the $q$-expansion function field of full level over $\mathbb{Q}$, and let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj`, whose field `Meta` is a `CurveModel` for $\bar{\mathbb{Q}}$ and $\bar{\mathbb{Q}}(X_H(M)) =$ `xHFunctionFieldBar M H`, with `eeta` identifying `Meta.C` with the generic fibre of $\mathfrak{X}$. Let $A$ be a valuation subring of $\bar{\mathbb{Q}}$ with $p$ in its nonunits, with algebraically closed residue field $\kappa$ of characteristic $p$, and let $\rho : R_p \to A$ lift the structure map to $\bar{\mathbb{Q}}$. Further data: a unit $pb$ of $(\mathbb{Z}/(M/p))^\times$ whose underlying residue is $p$; the operator $\delta$ on places of `Fbar` given by the semilinear action of the diamond automorphism `diamondActionModL` at a $\Gamma_0(M/p)$-lift of $pb$; a finset $SS$ enumerating the supersingular node pairs $(s_1,s_2)$, those with $s_2$ supersingular and $s_1$ its mod-$p$ Frobenius place; a $\bar{\mathbb{Q}}$-algebra automorphism $\theta$ of `xHFunctionFieldBar M H`; an integral $\bar{\mathbb{Q}}$-algebra map $\alpha$ from `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` with $\theta \circ \alpha$ also integral and with $\alpha$ the identity on Laurent-series coefficients; a place specialisation $Psp$ and a prolongation datum $Rpd$ for $Psp$ and $\theta$, subject to the type dichotomy and to $Rpd$ being a model for $(\alpha, \theta \circ \alpha, \delta)$; the $\theta$-equivariance `hwgen` of the point–place dictionary of `Meta`; and two readings `hcompat`, `hcompat'` expressing, for each $i \in \{0,1\}$, how the place of a closed point of the fibre curve model $\mathfrak{X}$`.Mfib` attached to a section is computed by $Psp.$`reduceFst` $W = Psp.sp(W|_\alpha)$ and $Psp.$`reduceSnd` $W = \delta(Psp.sp(W|_{\theta\circ\alpha}))$ together with the mod-$p$ Frobenius place operator. The conclusion: for every place $W$ of `xHFunctionFieldBar M H` over $\bar{\mathbb{Q}}$ satisfying `IsStrictFst`, i.e. $\delta(\mathrm{Frob}_p(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$ while $\mathrm{reduceFst}\,W$ does not satisfy the predicate `Fixed` for $\delta$, there exist a morphism $u$ from $\operatorname{Spec} A$ to $X_p(\Gamma_M)$ over $\operatorname{Spec} R_p$ via $\rho$, a morphism $u_\kappa$ from $\operatorname{Spec}\kappa$ to the fibre of the model at $\mathrm{residue} \circ \rho$, and a closed point $P_0$ of $\mathfrak{X}$`.Mfib A hA ρ hρ` such that: `barPt A` followed by $u$ agrees with the $\bar{\mathbb{Q}}$-point corresponding to $W$ under `Meta.pointEquivPlace` followed by `eeta` and the first projection; $u_\kappa$ followed by the first projection equals $\operatorname{Spec}$ of the residue map followed by $u$, and $u_\kappa$ followed by the second projection is the identity; the component map of index $0$, precomposed with $\mathfrak{X}$`.efib`, sends $P_0$ to the image under $u_\kappa$ of the closed point of $A$; the place of $P_0$ in the fibre curve model is $\mathrm{reduceFst}\,W$; and that image point is not in the range of the base map of the component of index $1$.
--
--   This is the existence half of the residue-disc dictionary for the Deligne–Rapoport model of $X_H(M)$ at a prime exactly dividing the level: a place of the first kind in the strict sense is the generic reading of an $A$-valued section whose special point is a smooth point of the first component and avoids the second. It is used by [`ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst`](thm.html#ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst) and [`ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict`](thm.html#ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict) in the analysis of the local parameters at the supersingular nodes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_section_comp_zero_placeOfPoint_eq_reduceFst_of_isStrictFst.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_section_comp_zero_placeOfPoint_eq_reduceFst_of_isStrictFst
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
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) :
    ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W →
      ∃ (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C),
        barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧
        uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1 ∧
        uκ ≫ pullback.snd _ _ = 𝟙 _ ∧
        (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceFst α hα W ∧
        uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 1).base := by sorry
