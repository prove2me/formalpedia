-- Prove2me | Theorems.Thm_Matrix_UnitaryGroup_haar_orbit_indicator_eq
-- name    : Matrix.UnitaryGroup.haar_orbit_indicator_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:26.738073+00:00
-- url     : https://prove2.me/theorems/915315af-c52b-4bb4-82a6-75e44fccf898
-- title:
--   Unitary Group: haar orbit indicator eq
-- statement:
--   For any Borel set `B ⊆ ℙ ℂ V` and any two base points
--   `p₀, p`, the Haar mass of the set `{U | U • p ∈ B}` equals that of
--   `{U | U • p₀ ∈ B}`.
--
--   Proof: take `V_p` with `V_p • p₀ = p` (from `IsPretransitive`, which
--   auto-includes `[Nonempty ι]` from the section variable). Then
--   `{U | U • p ∈ B} = (· * V_p) ⁻¹' {U | U • p₀ ∈ B}` by `smul_smul`.
--   Right-invariance of Haar measure gives the measure equality.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/FubiniStudyUnique.lean#L117-L138
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/FubiniStudyUnique.lean#L117-L138

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudy
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_UnitaryTransitive
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudyUnique
set_option autoImplicit false
@[expose] public section
public section
open Matrix
open scoped LinearAlgebra.Projectivization
open Matrix Matrix.UnitaryGroup
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem Matrix.UnitaryGroup.haar_orbit_indicator_eq
    {B : Set (ℙ ℂ (EuclideanSpace ℂ ι))} (hB : MeasurableSet B)
    (p₀ p : ℙ ℂ (EuclideanSpace ℂ ι)) :
    unitaryHaarProb {U : Matrix.unitaryGroup ι ℂ | U • p ∈ B}
      = unitaryHaarProb {U : Matrix.unitaryGroup ι ℂ | U • p₀ ∈ B} := by sorry
