-- Prove2me | Theorems.Thm_GlobalTheory_MaxLatStruct_int_of_unif
-- name    : GlobalTheory.MaxLatStruct.int_of_unif
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:54:30.554261+00:00
-- url     : https://prove2.me/theorems/323ac2d7-1af3-4d01-8262-9e8b35d9629e
-- title:
--   Max Lat Struct: int of unif
-- statement:
--   The Max Lat Struct construction uses the int of unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L72-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L72-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.MaxLatStruct
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem GlobalTheory.MaxLatStruct.int_of_unif {P : Ideal R} (hP : P.IsMaximal) {π b : R} (h1 : π ∈ P) (h2 : π ∉ P ^ 2) {α : K}
    (hα : ∀ p ∈ P, algebraMap R K p * α ∈ (1 : Submodule R K)) (hb : b ∈ P)
    (e : algebraMap R K π * α = algebraMap R K b) : α ∈ (1 : Submodule R K) := by sorry
