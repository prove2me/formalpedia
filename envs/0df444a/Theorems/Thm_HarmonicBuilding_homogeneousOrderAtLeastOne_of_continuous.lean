-- Prove2me | Theorems.Thm_HarmonicBuilding_homogeneousOrderAtLeastOne_of_continuous
-- name    : HarmonicBuilding.homogeneousOrderAtLeastOne_of_continuous
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-24T04:46:19.062163+00:00
-- url     : https://prove2.me/theorems/8909f9ff-e814-4b76-80dd-fbfb0e5e66be
-- title:
--   Continuous homogeneous harmonic maps have order at least one
-- statement:
--   Let h be a nonconstant homogeneous Korevaar--Schoen harmonic map of order alpha from the plane into a conical Euclidean building. If h is continuous, then alpha >= 1. This is the corrected (continuous) variant of HarmonicBuilding.homogeneousOrderAtLeastOne, which was disproved on 2026-09-06/07 by an explicit order-0 counterexample exploiting the same null-set loophole: the KS energy is a Filter.liminf of difference quotients, so the weak predicate IsPlanarKSHarmonicOn admits discontinuous minimizers. The continuity hypothesis blocks the loophole (a continuous a.e.-constant map is constant, contradicting NonconstantOn). This homogeneous order gap is the analytic core of the order gap of Gromov and Schoen: via the tangent-map reduction, a nonconstant harmonic map of order alpha < 1 would blow up to a nonconstant continuous homogeneous harmonic map of the same order, contradicting this statement. It is the child that HarmonicBuilding.orderAtLeastOne needs.
-- source:
--   Gromov--Schoen order gap (Publ. Math. IHES 76, 1992, Theorem 6.3) in its homogeneous form; recalled in Section 2 of Breiner--Dees, Harmonic maps into Euclidean buildings, arXiv:2604.16608. Corrected variant of HarmonicBuilding.homogeneousOrderAtLeastOne (disproved 2026-09-06/07 via the null-set/a.e.-constant loophole); the added continuity hypothesis blocks it. Child of HarmonicBuilding.orderAtLeastOne (2fa4f3d3): supplies the homogeneous order gap its tangent-map route needs.

import Mathlib

namespace HarmonicBuilding

/-- Restated interface: the mission definitions module
(`Definitions.Def_frame_2026_harmonic_building_conical`) is unavailable in the
publishing workspace (verified absent locally, on the build VM, in the
`junyi/lean-workspace` repo, and via the platform API), so the interface it
provides is restated here. The finite Coxeter data of the Euclidean building. -/
axiom EuclideanCoxeterData : ℕ → Type

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

/-- Restated: `h` is nonconstant on the set. -/
def NonconstantOn {X : Type*} (h : ℂ → X) (s : Set ℂ) : Prop :=
  ∃ x ∈ s, ∃ y ∈ s, h x ≠ h y

end HarmonicBuilding

namespace HarmonicBuilding

theorem homogeneousOrderAtLeastOne_of_continuous
    {N : ℕ} (C : EuclideanCoxeterData N) (M : ConicalBuildingModel N C)
    (h : ℂ → ConicalBuildingModel.carrier M) (alpha : ℝ)
    (hhom : IsHomogeneousOfOrderOn M Set.univ h 0 alpha)
    (hharm : IsPlanarKSHarmonicOn Set.univ h)
    (hcont : Continuous h)
    (hnc : NonconstantOn h Set.univ) :
    1 ≤ alpha := by sorry

end HarmonicBuilding
