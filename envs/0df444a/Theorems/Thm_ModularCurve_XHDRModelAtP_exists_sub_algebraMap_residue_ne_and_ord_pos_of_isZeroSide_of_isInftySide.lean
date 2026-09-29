-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_sub_algebraMap_residue_ne_and_ord_pos_of_isZeroSide_of_isInftySide
-- name    : ModularCurve.XHDRModelAtP.exists_sub_algebraMap_residue_ne_and_ord_pos_of_isZeroSide_of_isInftySide
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/8d5be29c-22b7-509d-92f6-37ed8be478f4
-- title:
--   A separator t_∞-a at zero-side places over an ∞-side reading
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, and assume $j(q) \in$ `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj` datum, so in particular a curve model `𝔛.Meta` over $\overline{\mathbb{Q}}$ with function field $F_M =$ `xHFunctionFieldBar M H`, together with its fibre data at $p$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit, with algebraically closed residue field $\kappa$ of characteristic $p$, and $\rho : R_p \to A$ a lift of `algebraMap (R p) (AlgebraicClosure ℚ)`. Let $pb$ be a unit of $\mathbb{Z}/(M/p)$ represented by $p$, and let $\delta$ act on places of $\bar F =$ `Fbar p M H hpM κ` through the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` of the $\Gamma_0(M/p)$-lift of $pb$. Let $\theta$ be an automorphism of $F_M$ over $\overline{\mathbb{Q}}$ inducing on places of `𝔛.Meta` the action of the isomorphism `𝔛.w` (hypothesis `hwgen`), let $\alpha : F_{M/p} \to F_M$ be an $\overline{\mathbb{Q}}$-algebra map which is the identity on Laurent series and is integral, with $\theta \circ \alpha$ also integral. Let `Psp` be a place-specialization datum for $(p,M,H,A)$ and `Rpd` a prolongation datum for it and $\theta$, consisting of two regular prolongations $R_1,R_2$ of $A$ to $F_M$ with values in $\bar F$; assume `hres₂α`, that on elements $\alpha v$ lying in both $R_1$ and $R_2$ the second residue is the $p$-power $q$-expansion Frobenius of the first, and `hcomp`, the compatibility of the two components of the fibre of $\mathfrak{X}$ over $\kappa$ with the two readings `Psp.reduceFst α` and `Psp.reduceSnd (θ ∘ α) δ` of places. Let $v$ be a place of $\bar F$ over $\kappa$ which is the first reading of some $\infty$-side place, let $ft \in F_M$ have $q$-expansion $j(q^p)\cdot j(q)^{-p}$, and let $W$ be a place of $F_M$ over $\overline{\mathbb{Q}}$ which is a zero-side place (cuspidal in the sense of `IsCuspidal'`, with $j(q)/j(q^p)^p$ taking at $W$ a value in $A$ with residue $1$) whose first reading is $v$. Then there is an $a \in A$ such that $ft - a$ lies in the integers of $R_1$, the residue $R_1(ft-a) \in \bar F$ does not have value $0$ at $v$, and $\mathrm{ord}_W(ft - a) > 0$.
--
--   This provides the separating function at the zero-side places lying over the first reading of an $\infty$-side cusp: the shifted Hasse-type parameter $t_\infty - a$ is a unit at $v$ after reduction while vanishing to positive order at $W$. It is used to produce a cusp chart at an $\infty$-side place, in [`ModularCurve.XHDRModelAtP.exists_isCuspChartFstAt_of_isInftySide_prolongationDatum`](thm.html#ModularCurve.XHDRModelAtP.exists_isCuspChartFstAt_of_isInftySide_prolongationDatum), within the analysis of the two cusps above $\infty$ on the reduction at $p$ of $X_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_sub_algebraMap_residue_ne_and_ord_pos_of_isZeroSide_of_isInftySide.lean

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

theorem ModularCurve.XHDRModelAtP.exists_sub_algebraMap_residue_ne_and_ord_pos_of_isZeroSide_of_isInftySide
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

    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

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
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hv : ∃ c, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) c ∧ (Psp.reduceFst α hα) c = v)
    (ft : ↥(xHFunctionFieldBar M H))
    (hft : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((ft : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) * ((jqModC (AlgebraicClosure ℚ))⁻¹) ^ p)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hW : (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) W) (hWv : Psp.reduceFst α hα W = v) :
    ∃ (a : ↥A) (h₁ : ft - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) ∈ Rpd.R₁.integers),
      ¬ v.HasValue (Rpd.R₁.residue ⟨_, h₁⟩) (0 : ResidueField ↥A) ∧
      0 < W.ord (ft - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) := by sorry
