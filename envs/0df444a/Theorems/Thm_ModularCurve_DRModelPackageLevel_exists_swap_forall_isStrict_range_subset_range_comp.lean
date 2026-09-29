-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_swap_forall_isStrict_range_subset_range_comp
-- name    : ModularCurve.DRModelPackageLevel.exists_swap_forall_isStrict_range_subset_range_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/a167a32d-b9d8-5168-961c-418715533da1
-- title:
--   Strict places reduce onto one Deligne–Rapoport component, off the other
-- statement:
--   Fix $N_0$ and a prime $p$ with $p \nmid N_0$, a package $\mathfrak P$ of type `DRModelPackageLevel N₀ p hpN₀` (carrying the model `X N₀ p` over `Spec (R p)`, its geometric curve model `𝔓.Meta` of the function field `modularFunctionFieldBar (N₀ * p)` together with the comparison isomorphism `𝔓.eeta`, and the data of the special fibre: the curve `𝔓.Mfib`, its comparison `𝔓.efib`, the structure maps `𝔓.π`, `𝔓.w` and the two morphisms `𝔓.comp … 0`, `𝔓.comp … 1`), a valuation subring $A$ of $\overline{\mathbf Q}$ with $p$ a nonunit of $A$, and a ring map $\rho : R(p) \to A$ whose composition with the inclusion $A \hookrightarrow \overline{\mathbf Q}$ is the structure map; consequently the residue field $\kappa$ of $A$ has characteristic $p$. Fix further `data : ModularPolynomialData p` satisfying the Kronecker congruence $\Phi \bmod p = (C X^p - X)(C X - X^p)$, integrality of the two Hecke maps `heckeAlphaBar`, `heckeBetaBar` at level $N_0$ and prime $p$, a place specialisation $P$ over $A$ with target field $\kappa$ and reduction map `IsLocalRing.residue A`, a prolongation tuple $R$ for $P$, and hypotheses that $R$ is a model and satisfies the fixed-place order law. Assume two compatibility hypotheses: for every $\overline{\mathbf Q}$-point $y$ of `𝔓.Meta.C` over the base, every $A$-point $u$ of `X N₀ p` over `Spec ρ` agreeing with $y$ generically, every $\kappa$-point $u_\kappa$ of the fibre lifting $u$ modulo the maximal ideal and sectioning the fibre structure, and assuming that the place `𝔓.Meta.pointEquivPlace y` is strict of the first or of the second kind (i.e. geometric Frobenius carries `P.reduceFst` of it to `P.reduceSnd`, respectively `P.reduceSnd` to `P.reduceFst`, and its square moves the relevant reduction), every closed point $P_0$ of `𝔓.Mfib` whose image under `𝔓.efib` is the image of the closed point under $u_\kappa$ followed by `fibreMap0 𝔓.π` has `placeOfPoint P₀ = P.reduceFst` of that place, and correspondingly with `fibreMap 𝔓.w.hom` inserted and `P.reduceSnd` on the right. The conclusion asserts the existence of a Boolean `swap` such that for every place $V$ of `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbf Q}$, every $A$-point $s$ of `X N₀ p` over `Spec ρ` whose generic point is the point of `𝔓.Meta.C` corresponding to $V$ under `pointEquivPlace`, and every $\kappa$-point $y$ of the fibre with $y$ followed by the first projection equal to `Spec (residue A)` followed by $s$ and $y$ followed by the second projection the identity: if `P.IsStrictFst V` then the range of the underlying map of $y$ is contained in the range of the component indexed by `if swap then 1 else 0` and not in that of the other component, and if `P.IsStrictSnd V` then the two indices are exchanged.
--
--   This is the scheme-theoretic counterpart, on the Deligne–Rapoport model of $X_0(N_0p)$, of the valuation-theoretic notion of strictness: a strict place of the first (respectively second) kind reduces to a point lying on exactly one of the two components of the special fibre, and a single global orientation bit governs which. It feeds the construction of places attached to points of the Jacobian in [`ModularCurve.DRModelPackageLevel.extendsToPlace_pts_of_isGoodClass`](thm.html#ModularCurve.DRModelPackageLevel.extendsToPlace_pts_of_isGoodClass).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_swap_forall_isStrict_range_subset_range_comp.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra IsLocalRing
  ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.exists_swap_forall_isStrict_range_subset_range_comp
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

      (_hcompatFst : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P0 : closedPoints (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).C),
          (𝔓.efib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).base P0.1 =
              (uκ ≫ fibreMap0 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base (IsLocalRing.closedPoint (ResidueField ↥A)) →
            (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).placeOfPoint P0 = P.reduceFst (𝔓.Meta.pointEquivPlace y))
      (_hcompatSnd : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P1 : closedPoints (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).C),
          (𝔓.efib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).base P1.1 =
              (uκ ≫ fibreMap 𝔓.w.hom 𝔓.w_over ((IsLocalRing.residue ↥A).comp ρ) ≫ fibreMap0 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base
                (IsLocalRing.closedPoint (ResidueField ↥A)) →
            (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).placeOfPoint P1 = P.reduceSnd (𝔓.Meta.pointEquivPlace y)),
    ∃ swap : Bool,
      ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))
        (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
        (_hs : Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 =
          ((𝔓.Meta.pointEquivPlace).symm V).1 ≫ 𝔓.eeta ≫
            pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ)))))
        (y : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
        (_hy₁ : y ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1)
        (_hy₂ : y ≫ pullback.snd _ _ = 𝟙 _),
        (P.IsStrictFst V →
          Set.range y.base ⊆ Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) (if swap then 1 else 0)).base ∧
          ¬ Set.range y.base ⊆ Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) (if swap then 0 else 1)).base) ∧
        (P.IsStrictSnd V →
          Set.range y.base ⊆ Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) (if swap then 0 else 1)).base ∧
          ¬ Set.range y.base ⊆ Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) (if swap then 1 else 0)).base) := by sorry
