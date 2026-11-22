-- Prove2me | Theorems.Thm_Matrix_UnitaryGroup_fsMeasure_unique
-- name    : Matrix.UnitaryGroup.fsMeasure_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:20.990078+00:00
-- url     : https://prove2.me/theorems/7b642678-43f9-4541-85b7-e9745edd0284
-- title:
--   Unitary Group: fs Measure unique
-- statement:
--   **Uniqueness of the `U(N)`-invariant probability measure**
--   on `ℂℙ^(N-1)`: any invariant probability measure `μ` equals
--   `fsMeasure p₀`. (`[Nonempty ι]` is required by the implicit
--   transitivity-instance synthesis through `haar_orbit_indicator_eq`,
--   auto-included from the section variable.)
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/FubiniStudyUnique.lean#L161-L232
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/FubiniStudyUnique.lean#L161-L232

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

theorem Matrix.UnitaryGroup.fsMeasure_unique
    (p₀ : ℙ ℂ (EuclideanSpace ℂ ι))
    (μ : MeasureTheory.Measure (ℙ ℂ (EuclideanSpace ℂ ι)))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hμ_inv : ∀ U : Matrix.unitaryGroup ι ℂ,
       MeasureTheory.Measure.map (fun p => U • p) μ = μ) :
    μ = fsMeasure p₀ := by sorry
