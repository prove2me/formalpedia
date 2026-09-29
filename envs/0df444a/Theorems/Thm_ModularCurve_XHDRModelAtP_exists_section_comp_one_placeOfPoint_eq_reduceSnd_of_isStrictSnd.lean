-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_section_comp_one_placeOfPoint_eq_reduceSnd_of_isStrictSnd
-- name    : ModularCurve.XHDRModelAtP.exists_section_comp_one_placeOfPoint_eq_reduceSnd_of_isStrictSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/41572b39-868d-5522-8a25-18260ab60a9a
-- title:
--   Strict second-kind places as A-sections closing on the second component
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial; assume $j$ lies in the $q$-expansion function field of $\mathrm{SL}_2(\mathbb{Z})$ over $\mathbb{Q}$ (hypothesis `hj`) and let $\mathfrak{X}$ be a Deligne–Rapoport model datum `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ in its nonunits, algebraically closed residue field $\kappa$ of characteristic $p$, and let $\rho : R_p \to A$ be a ring map compatible with $R_p \to \overline{\mathbb{Q}}$. Let $pb$ be a unit of $\mathbb{Z}/(M/p)$ represented by $p$, and let $\delta$ be the action on places of $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ` by the semilinear automorphism attached to the diamond automorphism `diamondActionModL` of the lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36); let $SS$ be a finset whose elements are exactly the pairs $(w_1,w_2)$ with $w_2$ supersingular and $w_1$ the mod-$p$ Frobenius translate of $w_2$ (`ssNodePairsQExp`). Let $\theta$ be an $\overline{\mathbb{Q}}$-automorphism of $F_M =$ `xHFunctionFieldBar M H`, and $\alpha : F_{M/p} \to F_M$ an $\overline{\mathbb{Q}}$-algebra map with $\alpha$ and $\theta \circ \alpha$ integral and with $\alpha$ the identity on underlying Laurent series; let $Psp$ be a `JHPlaceSpecialization` and $Rpd$ a `ProlongationDatum` for $Psp$ and $\theta$, satisfying the dichotomy `TypeDichotomy` and the model conditions `IsModel` for $\alpha, \theta\circ\alpha, \delta$. Assume further: $(\mathrm{hwgen})$ two $\overline{\mathbb{Q}}$-points $y, y'$ of $\mathfrak{X}.\mathrm{Meta}$ whose images in the generic fibre differ by $\mathfrak{X}.w$ have places differing by $\theta$; $(\mathrm{hcompat})$ for each $i \in \{0,1\}$, any $\overline{\mathbb{Q}}$-point $y$, any $A$-section $u$ of `toBase p (ΓM M H) hj` along $\mathrm{Spec}\,\rho$ with generic point $y$, any section $u_\kappa$ of the $\kappa$-fibre reducing $u$, and any closed point $P_0$ of $\mathfrak{X}.\mathrm{Mfib}$ sent by $\mathfrak{X}.\mathrm{efib}$ followed by the $i$-th component map to the closed point of $u_\kappa$, the place of $P_0$ is $Psp.\mathrm{reduceFst}\,\alpha$ applied to the place of $y$ when $i = 0$ and $Psp.\mathrm{reduceSnd}\,(\theta\circ\alpha)\,\delta$ applied to it when $i = 1$; $(\mathrm{hcompat}')$ under the same data, $Psp.\mathrm{reduceSnd}(\ldots)$ equals $\delta$ of the mod-$p$ Frobenius translate of the place of $P_0$ when $i = 0$, and $Psp.\mathrm{reduceFst}(\ldots)$ equals that Frobenius translate when $i = 1$. Then for every place $W$ of $F_M$ over $\overline{\mathbb{Q}}$ with $Psp.\mathrm{IsStrictSnd}$, that is $\mathrm{reduceFst}\,\alpha\,W$ equal to the Frobenius translate of $r := \mathrm{reduceSnd}\,(\theta\circ\alpha)\,\delta\,W$ and $r$ not satisfying `Fixed` for $\delta$, there exist an $A$-section $u$, a $\kappa$-section $u_\kappa$ of the fibre, and a closed point $P_0$ of $\mathfrak{X}.\mathrm{Mfib}$ such that $u$ has generic point the $\overline{\mathbb{Q}}$-point corresponding to $W$, $u_\kappa$ reduces $u$ and is a section of the base, $P_0$ is carried by $\mathfrak{X}.\mathrm{efib}$ followed by the component map of index $1$ to the closed point of $u_\kappa$, the place of $P_0$ equals $r$, and the closed point of $u_\kappa$ is not in the image of the component map of index $0$.
--
--   This is the second-kind counterpart of the corresponding statement for places of the first kind: strict places of the second kind are realised as $A$-valued sections of the Deligne–Rapoport model whose special point is a smooth point of the second component of the mod-$p$ fibre, read off by the second reduction map, and off the first component. It supplies the sections on which the residue-disc and discriminant-parameter computations are performed, and is used by [`ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictSnd`](thm.html#ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictSnd) and by [`ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict`](thm.html#ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_section_comp_one_placeOfPoint_eq_reduceSnd_of_isStrictSnd.lean

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

theorem ModularCurve.XHDRModelAtP.exists_section_comp_one_placeOfPoint_eq_reduceSnd_of_isStrictSnd
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
    ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W →
      ∃ (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C),
        barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧
        uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1 ∧
        uκ ≫ pullback.snd _ _ = 𝟙 _ ∧
        (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W ∧
        uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 0).base := by sorry
