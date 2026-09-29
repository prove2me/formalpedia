-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_not_isStrict_and_reduceFst_mem_of_range_subset_range_comp_inter
-- name    : ModularCurve.DRModelPackageLevel.not_isStrict_and_reduceFst_mem_of_range_subset_range_comp_inter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/05454fa6-64dd-5876-8374-3a30bcf7e1a9
-- title:
--   Crossing special point: non-strict place, supersingular first reduction
-- statement:
--   Fix $N_0 \ge 1$ and a prime $p$ with $p \nmid N_0$, a Deligne–Rapoport model package $\mathfrak P$ of level $N_0p$ over $R_p$ (with its proper flat integral normal model `toBase N₀ p : X N₀ p ⟶ Spec (R p)`, the curve model `𝔓.Meta` identifying $\overline{\mathbb Q}$-points of the generic fibre with places of `modularFunctionFieldBar (N₀ * p)`, and the remaining package data), a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$, and a ring map $\rho : R_p \to A$ inducing the structure map $R_p \to \overline{\mathbb Q}$; then the residue field of $A$ has characteristic $p$. Let `data` be modular polynomial data for $p$ satisfying the Kronecker congruence $\Phi \equiv (X^p - Y)(X - Y^p) \bmod p$, let $h\alpha, h\beta$ be the integrality hypotheses for the two degeneracy embeddings $\mathrm{modularFunctionFieldBar}(N_0) \to \mathrm{modularFunctionFieldBar}(N_0p)$, let $P$ be a place specialisation at $A$ with values in places over the residue field of $A$ along `IsLocalRing.residue`, and let $R$ be a prolongation tuple for $P$ which is a model (the two divisor laws and the cusp laws at $\infty$ and $0$) and has fixed order law. Let $V$ be a place of `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbb Q}$, let $s$ be an $A$-point of the model over $\rho$ whose base change to $\overline{\mathbb Q}$ is the generic-fibre point attached to $V$ through `𝔓.Meta.pointEquivPlace` and `𝔓.eeta`, and let $y$ be a section of the base change of the model along the residue map $A \to \mathrm{ResidueField}\,A$ composed with $\rho$, reducing $s$ (its first projection is $\mathrm{Spec}$ of the residue map followed by $s$, its second projection the identity). The assertion is: if the topological image of $y$ is contained both in the image of `𝔓.comp … 0` and in the image of `𝔓.comp … 1`, the two morphisms of index $0$ and $1$ supplied by the package for the fibre over the residue field, then $V$ is not strict of the first kind (it is not the case that $\varphi(\mathrm{reduceFst}\,V) = \mathrm{reduceSnd}\,V$ with $\varphi^2(\mathrm{reduceFst}\,V) \ne \mathrm{reduceFst}\,V$, where $\varphi$ is `frobOnPlacesGeomLevel`), nor strict of the second kind (the corresponding condition with the roles of $\mathrm{reduceFst}$ and $\mathrm{reduceSnd}$ exchanged), and $\mathrm{reduceFst}\,V$ lies in `ssPlaces p N₀ (ResidueField ↥A)`, the set of places satisfying `IsSupersingularPlace p N₀`.
--
--   This is the implication, from the geometry of the section of a point to the combinatorics of its place, in the dictionary between the two components of the special fibre of the Deligne–Rapoport model of $X_0(N_0p)$ and the types of places attached to a place specialisation: a point whose section meets both components, i.e. reduces to a crossing, has a place that is neither strict of the first nor of the second kind, and whose first reduction is supersingular. It is used in [`ModularCurve.DRModelPackageLevel.extendsToPlace_pts_smul_sub`](thm.html#ModularCurve.DRModelPackageLevel.extendsToPlace_pts_smul_sub).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_not_isStrict_and_reduceFst_mem_of_range_subset_range_comp_inter.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.not_isStrict_and_reduceFst_mem_of_range_subset_range_comp_inter
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N₀
    ∀ (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (P : PlaceSpecialization A p N₀ data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P) (_hmodel : R.IsModel) (_hO : R.OrderLawFixed)
      (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))
      (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
      (_hs : Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 =
        ((𝔓.Meta.pointEquivPlace).symm V).1 ≫ 𝔓.eeta ≫
          pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ)))))
      (y : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
      (_hy₁ : y ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1)
      (_hy₂ : y ≫ pullback.snd _ _ = 𝟙 _),
      (Set.range y.base ⊆ Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) 0).base ∧
          Set.range y.base ⊆ Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) 1).base) →
        ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧ P.reduceFst V ∈ ssPlaces p N₀ (ResidueField ↥A) := by sorry
