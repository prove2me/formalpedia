-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_isZeroSide_iff_isInftySide_smul_prolongationDatum
-- name    : ModularCurve.XHDRModelAtP.isZeroSide_iff_isInftySide_smul_prolongationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/77ab87e1-de4d-57d2-a95d-aeb9426ee24a
-- title:
--   Atkin–Lehner twist exchanges zero-side and infinity-side places
-- statement:
--   Fix a prime $p$ and a nonzero modulus $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that maps to $1$ under `ZMod.unitsMap` along $(M/p) \mid M$, with $M/p$ nonzero, and assume $j$ (as the Laurent series `jqModC ℚ`) lies in the $q$-expansion function field of $\mathrm{SL}_2(\mathbb{Z})$; let $\mathfrak{X}$ be a model bundle `XHDRModelAtP p M H hpM hj` over $R_p$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ be a ring map compatible with $R_p \to \overline{\mathbb{Q}}$. Further data: a unit $pb$ of $\mathbb{Z}/(M/p)$ represented by $p$; the self-map $\delta$ of places of $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ` over $\kappa$ given by the action of the semilinear automorphism attached to the diamond automorphism `diamondActionModL` at level $M/p$ and subgroup `infSubgroup p M H hpM` evaluated at [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36); a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M =$ `xHFunctionFieldBar M H` pinned by the requirement (hypothesis `hwgen`) that for $\overline{\mathbb{Q}}$-points $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, if $y'$ followed by $\mathfrak{X}.\mathrm{eeta}$, the first pullback projection and $\mathfrak{X}.w.\mathrm{hom}$ agrees with $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and that projection, then the place of $y'$ is the $\theta$-translate of the place of $y$; a $\overline{\mathbb{Q}}$-algebra map $\alpha$ from `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` to $F_M$ acting as the identity on the underlying Laurent series, with $\alpha$ and $\theta \circ \alpha$ integral; a specialization datum $Psp$ of places (`JHPlaceSpecialization p M H hpM A`) and a prolongation datum $Rpd$ for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residues in $\bar F$, $R_1$ computing residues coefficientwise on Laurent series and $R_2$ obtained from $R_1$ by precomposition with $\theta$. The compatibility hypothesis `hcomp` requires, for each $i \in \{0,1\}$, each $\overline{\mathbb{Q}}$-point $y$, each $A$-section $u$ of the model over $\operatorname{Spec} \rho$ with $\mathrm{barPt}\,A$ followed by $u$ equal to $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first projection, each $\kappa$-point $u_\kappa$ of the fibre of the model over the residue map composed with $\rho$ that reduces $u$ and splits the base projection, and each closed point $P_0$ of the fibre curve $(\mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$ lying over the closed point image of $u_\kappa$ through $\mathfrak{X}.\mathrm{efib}$ followed by the $i$-th component map $\mathfrak{X}.\mathrm{comp}$, that the place of $P_0$ equal $Psp.\mathrm{reduceFst}\ \alpha$ applied to the place of $y$ when $i = 0$, and $Psp.\mathrm{reduceSnd}\ (\theta \circ \alpha)\ \delta$ applied to it otherwise. The conclusion is that for every place $W$ of $F_M$ over $\overline{\mathbb{Q}}$, $W$ is zero-side if and only if the $\theta$-translate of $W$ is infinity-side; here zero-side means that `IsCuspidal'` holds for $W$ and that there are $x, x' \in F_M$ with Laurent series $j$ and $j(q^p)$ (that is, `qExpand` of `jqModC` at $p$) respectively and some $\tau \in A$ with residue $1$ such that $W$ takes the value $\tau$ at $x/x'^p$, while infinity-side means that `IsCuspidal` holds for $W$ together with the same data with $x'/x^p$ in place of $x/x'^p$.
--
--   This is the cusp law for $X_H(M)$ at $p \parallel M$ in the form that the Atkin–Lehner automorphism of the model interchanges the two cuspidal families: the places reducing into the component indexed by $0$ and those reducing into the component indexed by $1$. It is used in the later analysis of the reductions of cusps, in [`ModularCurve.XHDRModelAtP.cuspLocalSemicontinuityZero_prolongationDatum_of_residue`](thm.html#ModularCurve.XHDRModelAtP.cuspLocalSemicontinuityZero_prolongationDatum_of_residue) and in [`ModularCurve.XHDRModelAtP.oneSidedSnd_laws_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel`](thm.html#ModularCurve.XHDRModelAtP.oneSidedSnd_laws_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_isZeroSide_iff_isInftySide_smul_prolongationDatum.lean

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

theorem ModularCurve.XHDRModelAtP.isZeroSide_iff_isInftySide_smul_prolongationDatum
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
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) W ↔ (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) (SemilinearAut.ofAlgAut θ • W) := by sorry
