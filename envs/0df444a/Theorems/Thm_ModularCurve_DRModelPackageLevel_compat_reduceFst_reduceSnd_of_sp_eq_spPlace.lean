-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_compat_reduceFst_reduceSnd_of_sp_eq_spPlace
-- name    : ModularCurve.DRModelPackageLevel.compat_reduceFst_reduceSnd_of_sp_eq_spPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/d8fed520-b106-533d-b776-c9bf416df11f
-- title:
--   Strict points reduce to reduceFst and reduceSnd
-- statement:
--   Fix $N_0$ with $N_0 \neq 0$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak P$ be a `DRModelPackageLevel` for the data $(N_0,p)$: a model of the Igusa scheme `X N₀ p` over $\mathrm{Spec}\,R_p$ together with a curve model `Meta` for $\overline{\mathbf Q}$ and the field `modularFunctionFieldBar (N₀ * p)`, an isomorphism `eeta` onto the generic fibre, a forgetful morphism $\pi$ over the base and an involution $w$. Let $A$ be a valuation subring of $\overline{\mathbf Q}$ with $p$ a non-unit of $A$, and $\rho \colon R_p \to A$ a ring homomorphism whose composite with the inclusion of $A$ is the structure map $R_p \to \overline{\mathbf Q}$; the residue field $\kappa$ of $A$ then has characteristic $p$. Assume given modular polynomial data at $p$ with the Kronecker congruence `hKr`, integrality of the Hecke maps $\bar\alpha$ and $\bar\beta$ at level $N_0$, a fibre model `fm` of level $N_0$ over $(A, \kappa, \mathrm{residue})$ satisfying the cusp-chart conditions, the hypotheses that the `coeffEmb`-images of the Igusa chart algebras `chartAlgFin N₀ p` and `chartAlgInf N₀ p` lie in `fm.BFin` and `fm.BInf` respectively, surjectivity of $A \to \kappa$, modular polynomial data for every divisor of $N_0$, separability of the level-$N_0$ polynomial $\Phi$ reduced to $\kappa$ and viewed in $\kappa(X)$, and a place specialization $P$ (a map $\mathrm{sp}$ from places of `modularFunctionFieldBar N₀` over $\overline{\mathbf Q}$ to places of `modularFunctionFieldC κ N₀`, together with its Picard component and compatibility axioms) whose $\mathrm{sp}$ equals `fm.spPlace` for these data. Then two assertions hold. For every $\overline{\mathbf Q}$-point $y$ of `Meta.C` over the base, every morphism $u \colon \mathrm{Spec}\,A \to$ `X N₀ p` over $\mathrm{Spec}\,\rho$ whose restriction along $\mathrm{Spec}$ of the inclusion $A \hookrightarrow \overline{\mathbf Q}$ is $y$ transported through `eeta` and the generic-fibre projection, every $\kappa$-section $u_\kappa$ of the special fibre of `toBase N₀ p` along $\mathrm{residue} \circ \rho$ lying over $u$, and under the hypothesis that the place `Meta.pointEquivPlace y` is strict in the first or the second sense for $P$ (Frobenius on geometric places of level $N_0$ carries $P.\mathrm{reduceFst}$ to $P.\mathrm{reduceSnd}$ and does not fix the former after two applications, or the mirror condition), every closed point $P_0$ of the curve `𝔓.Mfib κ (residue ∘ ρ)` whose image under the base map of `𝔓.efib` is the image of the closed point of $\kappa$ under $u_\kappa$ followed by `fibreMap0 𝔓.π` satisfies `placeOfPoint P₀ = P.reduceFst (Meta.pointEquivPlace y)`, that is, $\mathrm{sp}$ applied to the restriction of the place of $y$ along $\bar\alpha$. The second assertion is the same statement with $u_\kappa$ followed by the fibre map of the involution $w$ and then by `fibreMap0 𝔓.π`, and with `P.reduceSnd`, i.e. $\mathrm{sp}$ of the restriction along $\bar\beta$.
--
--   This is the compatibility between the valuation-theoretic specialisation of places of $X_0(N_0)$ and the scheme-theoretic reduction of points of the Deligne–Rapoport model of $X_0(N_0p)$: at a strict place, the reduction of an $A$-point along the forgetful map, resp. along the partial Atkin–Lehner involution followed by the forgetful map, is computed by $\mathrm{reduceFst}$, resp. $\mathrm{reduceSnd}$. It is used in the construction of the Néron object at $p$ and its bridge to relative sub-Picard groups, and in the criterion for a divisor class to extend over the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_compat_reduceFst_reduceSnd_of_sp_eq_spPlace.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra IsLocalRing
  ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.compat_reduceFst_reduceSnd_of_sp_eq_spPlace
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N₀
    ∀ (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (fm : CharPModel.FibreModel N₀ A p (ResidueField ↥A) (IsLocalRing.residue ↥A))
      (cc : fm.CuspChart)
      (hfin : ∀ b : IgusaScheme.chartAlgFin N₀ p,
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull N₀)).2⟩ :
            laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N₀)) ∈ fm.BFin)
      (hinf : ∀ b : IgusaScheme.chartAlgInf N₀ p,
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull N₀)).2⟩ :
            laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N₀)) ∈ fm.BInf)
      (hred : Function.Surjective (IsLocalRing.residue ↥A))
      (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N₀ → ModularPolynomialData d)
      (hsepΦ : (((dataAll N₀ (dvd_refl N₀)).Φ.map
          (Polynomial.mapRingHom (Int.castRingHom (ResidueField ↥A)))).map
        (algebraMap (Polynomial (ResidueField ↥A)) (RatFunc (ResidueField ↥A)))).Separable)
      (P : PlaceSpecialization A p N₀ data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
      (hP : P.sp = fm.spPlace hred dataAll hsepΦ),
    (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P0 : closedPoints (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).C),
          (𝔓.efib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).base P0.1 =
              (uκ ≫ fibreMap0 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base (IsLocalRing.closedPoint (ResidueField ↥A)) →
            (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).placeOfPoint P0 = P.reduceFst (𝔓.Meta.pointEquivPlace y)) ∧
    (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P1 : closedPoints (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).C),
          (𝔓.efib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).base P1.1 =
              (uκ ≫ fibreMap 𝔓.w.hom 𝔓.w_over ((IsLocalRing.residue ↥A).comp ρ) ≫ fibreMap0 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base
                (IsLocalRing.closedPoint (ResidueField ↥A)) →
            (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).placeOfPoint P1 = P.reduceSnd (𝔓.Meta.pointEquivPlace y)) := by sorry
