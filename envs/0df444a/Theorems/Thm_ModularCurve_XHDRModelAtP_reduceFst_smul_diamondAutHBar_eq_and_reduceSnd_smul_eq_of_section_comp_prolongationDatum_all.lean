-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_reduceFst_smul_diamondAutHBar_eq_and_reduceSnd_smul_eq_of_section_comp_prolongationDatum_all
-- name    : ModularCurve.XHDRModelAtP.reduceFst_smul_diamondAutHBar_eq_and_reduceSnd_smul_eq_of_section_comp_prolongationDatum_all
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/e12f2483-d379-5a31-9663-0535d5023089
-- title:
--   Diamond equivariance of both readings of a configured place
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under `ZMod.unitsMap` to $(\mathbb{Z}/(M/p))^\times$ is $1$, the hypothesis `hj` that the $q$-expansion `jqModC ℚ` of $j$ lies in the rational function field at full level, and a Deligne–Rapoport datum $\mathfrak{X}$ of type `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over $R_p$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ in `A.nonunits`, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ lift `algebraMap (R p) (AlgebraicClosure ℚ)` along the inclusion of $A$. Further data: a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying element is $p$; a self-map $\delta$ of the places of `JHNeronObjectAtP.Fbar p M H hpM κ` over $\kappa$ given by the action, through `SemilinearAut.ofAlgAut`, of `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` applied to [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36), where `infSubgroup` is the image of $H$ in $(\mathbb{Z}/(M/p))^\times$; an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of `xHFunctionFieldBar M H` implementing $\mathfrak{X}.w$ on places, in the sense that whenever two $\overline{\mathbb{Q}}$-sections $y, y'$ of $\mathfrak{X}.\mathrm{Meta}$ satisfy that $y'$ followed by `eeta`, the first projection and $\mathfrak{X}.w.hom$ agrees with $y$ followed by `eeta` and the first projection, the place of $y'$ is $\theta$ applied to the place of $y$; an $\overline{\mathbb{Q}}$-algebra map $\alpha$ from `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` to `xHFunctionFieldBar M H` which is the identity on underlying Laurent series, with $\alpha$ and $\theta \circ \alpha$ integral; a place-specialisation packet `Psp` for $(p, M, H, A)$ and a prolongation datum `Rpd` for `Psp` and $\theta$. Assume the compatibility clause `hcomp`: for every index $i \in \{0,1\}$, every $\overline{\mathbb{Q}}$-section $y$, every $A$-point $u$ of $X$ over $\mathrm{Spec}\,\rho$ with `barPt A` followed by $u$ equal to $y$ followed by `eeta` and the first projection, every $\kappa$-point $u\kappa$ of the fibre over the residue map composed with $\rho$ whose projections are $u$ reduced and the identity, and every closed point $P_0$ of $\mathfrak{X}.\mathrm{Mfib}$ lying over the closed point of $u\kappa$ along `efib` followed by `comp … i`, the place of $P_0$ equals `Psp.reduceFst α hα` of the place of $y$ when $i = 0$, that is the specialisation of its restriction along $\alpha$, and `Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ` of that place when $i = 1$, that is $\delta$ of the specialisation of its restriction along $\theta \circ \alpha$. Then, for each $d \in (\mathbb{Z}/M)^\times$ and each such configuration $(i, y, u, u\kappa, P_0)$ with its compatibilities, both readings are diamond-equivariant: if $i = 0$ then `reduceFst` of the translate of the place of $y$ by `diamondAutHBar M H d` equals the translate, by `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` applied to [`CuspForm.gammaLift (M/p)`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of the image of $d$ in $(\mathbb{Z}/(M/p))^\times$, of `reduceFst` of the place of $y$; and if $i = 1$ the same identity holds with `reduceSnd (θ.toAlgHom.comp α) hβ δ` in place of `reduceFst`.
--
--   This records that the two component-wise reductions of a generic place of $X_H(M)$, read off from a configured section of the Deligne–Rapoport model at $p \parallel M$, commute with the diamond operators, the diamond $\langle d \rangle$ upstairs corresponding to $\langle \bar d \rangle$ at level $M/p$. It is used in the comparison of the two readings under the Atkin–Lehner automorphism $\theta$ and the associated strictness criterion, within the analysis of the reduction of the modular curve at $p$ that underlies level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_reduceFst_smul_diamondAutHBar_eq_and_reduceSnd_smul_eq_of_section_comp_prolongationDatum_all.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.reduceFst_smul_diamondAutHBar_eq_and_reduceSnd_smul_eq_of_section_comp_prolongationDatum_all
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

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hcomp : (∀ (i : Fin 2)
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
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)))
    (d : (ZMod M)ˣ) (i : Fin 2)
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) :
    (i = 0 → Psp.reduceFst α hα (SemilinearAut.ofAlgAut (diamondAutHBar M H d) • 𝔛.Meta.pointEquivPlace y) =
      SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d))) • Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)) ∧
    (i = 1 → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (SemilinearAut.ofAlgAut (diamondAutHBar M H d) • 𝔛.Meta.pointEquivPlace y) =
      SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d))) • Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)) := by sorry
