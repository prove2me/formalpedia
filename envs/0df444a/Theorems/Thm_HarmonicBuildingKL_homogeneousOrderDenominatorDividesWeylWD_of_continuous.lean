-- Prove2me | Theorems.Thm_HarmonicBuildingKL_homogeneousOrderDenominatorDividesWeylWD_of_continuous
-- name    : HarmonicBuildingKL.homogeneousOrderDenominatorDividesWeylWD_of_continuous
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-24T04:43:25.64317+00:00
-- url     : https://prove2.me/theorems/e2cfae4c-1fcd-4658-826c-742e6293fd7b
-- title:
--   The order of a continuous homogeneous harmonic map has denominator dividing the Weyl group
-- statement:
--   Let h be a nonconstant homogeneous Korevaar--Schoen harmonic map of order alpha from the plane into a conical Euclidean building of Coxeter type W carrying its Delta_mod direction structure. If h is continuous, then alpha = m/k for positive integers m, k with k dividing the order of the Weyl group. This is the corrected (continuous) variant of HarmonicBuildingKL.homogeneousOrderDenominatorDividesWeylWD, which was disproved on 2026-09-06/07 via an a.e.-constant order-0 'homogeneous harmonic' map: the KS energy is a Filter.liminf of difference quotients, so the weak predicate IsPlanarKSHarmonicOn admits discontinuous minimizers with zero energy. The continuity hypothesis blocks that null-set loophole (a continuous a.e.-constant map is constant, contradicting NonconstantOn). Mathematically this is the Breiner--Dees Theorem 2.15 angle-rigidity classification of homogeneous harmonic maps into buildings. It is the classifier the blow-up route of HarmonicBuildingKL.orderDenominatorDividesWeylWD needs.
-- source:
--   Breiner--Dees, Harmonic maps into Euclidean buildings, arXiv:2604.16608, Theorem 2.15 (angle rigidity for homogeneous harmonic maps). Corrected variant of HarmonicBuildingKL.homogeneousOrderDenominatorDividesWeylWD (disproved 2026-09-06/07 via the null-set/a.e.-constant loophole); the added continuity hypothesis blocks it. Child of HarmonicBuildingKL.orderDenominatorDividesWeylWD (545fce07): supplies the homogeneous classifier its blow-up route needs.

import Mathlib

namespace HarmonicBuildingKL

/-- Restated interface: the mission definitions modules
(`Definitions.Def_frame_2026_harmonic_building_conical`,
`Definitions.Def_euclidean_building_directions`) are unavailable in the
publishing workspace (verified absent locally, on the build VM, in the
`junyi/lean-workspace` repo, and via the platform API), so the interface they
provide is restated here. The finite Coxeter data of the Euclidean building. -/
axiom EuclideanCoxeterData : ℕ → Type

/-- Restated: the Weyl group of the Coxeter data. -/
axiom EuclideanCoxeterData.weyl : {N : ℕ} → EuclideanCoxeterData N → Type

/-- Restated: the Weyl group is finite. -/
axiom weyl_fintype {N : ℕ} (C : EuclideanCoxeterData N) :
    Fintype (EuclideanCoxeterData.weyl C)

attribute [instance] weyl_fintype

/-- Restated: a conical Euclidean building model of Coxeter type `C`. -/
axiom ConicalBuildingModel.{u} (N : ℕ) (C : EuclideanCoxeterData N) : Type u

/-- Restated: the carrier (underlying space) of the conical model. -/
axiom ConicalBuildingModel.carrier.{u, v} {N : ℕ} {C : EuclideanCoxeterData N}
    (M : ConicalBuildingModel.{u} N C) : Type v

/-- Restated: the carrier is a topological space, so continuity is meaningful. -/
axiom carrier_topological.{u, v} {N : ℕ} {C : EuclideanCoxeterData N}
    (M : ConicalBuildingModel.{u} N C) :
    TopologicalSpace (ConicalBuildingModel.carrier.{u, v} M)

attribute [instance] carrier_topological

/-- Restated: `h` is homogeneous of order `alpha` about the base point. -/
axiom IsHomogeneousOfOrderOn.{u, v} {N : ℕ} {C : EuclideanCoxeterData N}
    (M : ConicalBuildingModel.{u} N C) :
    Set ℂ → (ℂ → ConicalBuildingModel.carrier.{u, v} M) → ℂ → ℝ → Prop

/-- Restated: `h` is Korevaar--Schoen harmonic on the domain. -/
axiom IsPlanarKSHarmonicOn {X : Type*} [TopologicalSpace X] :
    Set ℂ → (ℂ → X) → Prop

/-- Restated: the building carries its Δ_mod direction structure. -/
axiom BuildingWithDirections (N : ℕ) (C : EuclideanCoxeterData N) : Type → Type

/-- Restated: `h` is nonconstant on the set. -/
def NonconstantOn {X : Type*} (h : ℂ → X) (s : Set ℂ) : Prop :=
  ∃ x ∈ s, ∃ y ∈ s, h x ≠ h y

end HarmonicBuildingKL

namespace HarmonicBuildingKL

theorem homogeneousOrderDenominatorDividesWeylWD_of_continuous
    {N : ℕ} (C : EuclideanCoxeterData N) (M : ConicalBuildingModel N C)
    (BM : BuildingWithDirections N C (ConicalBuildingModel.carrier M))
    (h : ℂ → ConicalBuildingModel.carrier M) (alpha : ℝ)
    (hhom : IsHomogeneousOfOrderOn M Set.univ h 0 alpha)
    (hharm : IsPlanarKSHarmonicOn Set.univ h)
    (hcont : Continuous h)
    (hnc : NonconstantOn h Set.univ) :
    ∃ m k : ℕ, 0 < m ∧ 0 < k ∧
      k ∣ Fintype.card C.weyl ∧ alpha = (m : ℝ) / (k : ℝ) := by sorry

end HarmonicBuildingKL
