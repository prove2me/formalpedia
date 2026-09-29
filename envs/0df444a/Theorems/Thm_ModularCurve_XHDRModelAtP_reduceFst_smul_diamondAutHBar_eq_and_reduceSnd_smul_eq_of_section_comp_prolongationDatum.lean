-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_reduceFst_smul_diamondAutHBar_eq_and_reduceSnd_smul_eq_of_section_comp_prolongationDatum
-- name    : ModularCurve.XHDRModelAtP.reduceFst_smul_diamondAutHBar_eq_and_reduceSnd_smul_eq_of_section_comp_prolongationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/26bd0f3d-696d-570d-aa6b-40901ac13a08
-- title:
--   Diamond equivariance of the two place reductions
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$, $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, and a witness $hj$ that $j$ lies in the $q$-expansion function field of $SL(2,\mathbb{Z})$; let $\mathfrak{X}$ be an `XHDRModelAtP` datum for these. Further data: a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ in its non-units, whose residue field $\kappa$ is algebraically closed of characteristic $p$; a lift $\rho : R_p \to A$ of the structure map; a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying element is $p$; the map $\delta$ on places of $\mathrm{Fbar}\,p\,M\,H$ over $\kappa$ given by the `diamondActionModL` automorphism at [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36); an automorphism $\theta$ of $\overline{\mathbb{Q}}$-algebra $\mathrm{xHFunctionFieldBar}\,M\,H$ realising the correspondence $\mathfrak{X}.w$ on places of $\overline{\mathbb{Q}}$-sections (hypothesis `hwgen`); an integral $\overline{\mathbb{Q}}$-algebra map $\alpha$ from $\mathrm{xHFunctionFieldBar}\,(M/p)\,(\mathrm{infSubgroup}\,p\,M\,H)$ to $\mathrm{xHFunctionFieldBar}\,M\,H$ which is the identity on Laurent series, with $\theta \circ \alpha$ also integral; a place-specialisation packet $Psp$ and a prolongation datum $Rpd$ for $Psp$ and $\theta$. The hypothesis `hcomp` says: for $i \in \{0,1\}$, a $\overline{\mathbb{Q}}$-section $y$ of $\mathfrak{X}.\mathrm{Meta}$, an $A$-point $u$ of the model extending $y$, a compatible $\kappa$-point $u\kappa$ of the special fibre, and a closed point $P_0$ of the fibre curve model lying over $u\kappa$ on the $i$-th component, the place of $P_0$ equals $Psp.\mathrm{reduceFst}\,\alpha$ applied to the place of $y$ when $i = 0$, and $Psp.\mathrm{reduceSnd}\,(\theta \circ \alpha)\,\delta$ applied to it when $i = 1$; here $\mathrm{reduceFst}\,W = Psp.\mathrm{sp}(W|_\alpha)$ and $\mathrm{reduceSnd}\,W = \delta(Psp.\mathrm{sp}(W|_{\theta \circ \alpha}))$. Given moreover $d \in (\mathbb{Z}/M)^\times$, such data $i, y, u, u\kappa, P_0$ with the same compatibilities, and the hypothesis that the image of $P_0$ lies off the range of every component $j \neq i$, the conclusion is the conjunction of two implications: if $i = 0$ then $\mathrm{reduceFst}\,\alpha$ applied to $\langle d \rangle$-translate of the place of $y$ (the translate by the semilinear automorphism attached to `diamondAutHBar M H d`) equals the translate of $\mathrm{reduceFst}\,\alpha$ of the place of $y$ by the semilinear automorphism attached to `diamondActionModL` at [`CuspForm.gammaLift (M / p)`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of the reduction of $d$ in $(\mathbb{Z}/(M/p))^\times$; and the same identity with $\mathrm{reduceSnd}\,(\theta \circ \alpha)\,\delta$ in place of $\mathrm{reduceFst}\,\alpha$ when $i = 1$.
--
--   This is the diamond-equivariance of the two component-wise readings of the place-specialisation packet on the Deligne–Rapoport model of $X_H(M)$ at a prime $p$ exactly dividing $M$: since the packet's specialisation map is given abstractly, equivariance for $\langle d \rangle$ is expressed through the hypothesis `hcomp` relating places of closed points in the special fibre to the two reductions, and is therefore stated separately for each of the two components. It feeds the transport by $\theta$ of the cusp semicontinuity statement on the zero component, in [`ModularCurve.XHDRModelAtP.cuspLocalSemicontinuityZero_prolongationDatum_of_residue`](thm.html#ModularCurve.XHDRModelAtP.cuspLocalSemicontinuityZero_prolongationDatum_of_residue).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_reduceFst_smul_diamondAutHBar_eq_and_reduceSnd_smul_eq_of_section_comp_prolongationDatum.lean

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

theorem ModularCurve.XHDRModelAtP.reduceFst_smul_diamondAutHBar_eq_and_reduceSnd_smul_eq_of_section_comp_prolongationDatum
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
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hnc : ∀ j : Fin 2, j ≠ i → (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 ∉ Set.range (𝔛.comp A hA ρ hρ j).base) :
    (i = 0 → Psp.reduceFst α hα (SemilinearAut.ofAlgAut (diamondAutHBar M H d) • 𝔛.Meta.pointEquivPlace y) =
      SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d))) • Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)) ∧
    (i = 1 → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (SemilinearAut.ofAlgAut (diamondAutHBar M H d) • 𝔛.Meta.pointEquivPlace y) =
      SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d))) • Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)) := by sorry
