-- Prove2me | Theorems.Thm_Matrix_UnitaryGroup_smul_comp_orbitMap
-- name    : Matrix.UnitaryGroup.smul_comp_orbitMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:57:03.425707+00:00
-- url     : https://prove2.me/theorems/dd8056fc-84a8-447a-aac1-92875ea2b591
-- title:
--   Unitary Group: smul comp orbit Map
-- statement:
--   Compatibility lemma: `(U' • ·) ∘ orbitMap p₀ = orbitMap p₀ ∘ (U' * ·)`.
--   The MulAction axiom `(U' * U) • p₀ = U' • (U • p₀)` makes the two
--   forms equal as functions.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/FubiniStudy.lean#L116-L121
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/FubiniStudy.lean#L116-L121

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_Unitary
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MeasureSpace
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Matrix_UnitaryHaar
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudy
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Matrix
open scoped LinearAlgebra.Projectivization
open Matrix Matrix.UnitaryGroup
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Matrix.UnitaryGroup.smul_comp_orbitMap (U' : Matrix.unitaryGroup ι ℂ)
    (p₀ : ℙ ℂ (EuclideanSpace ℂ ι)) :
    (fun p => U' • p) ∘ orbitMap p₀ = orbitMap p₀ ∘ (fun U => U' * U) := by sorry
