-- Prove2me | Theorems.Thm_GlobalTheory_MaxLatStruct_mem_of_int
-- name    : GlobalTheory.MaxLatStruct.mem_of_int
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:51:14.180835+00:00
-- url     : https://prove2.me/theorems/61c9b898-9850-4f40-b4b6-18cee32b709a
-- title:
--   Max Lat Struct: mem of int
-- statement:
--   The Max Lat Struct construction uses the mem of int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L112-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L112-L130

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
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule R V} {σ : R →+* R}
omit [IsDedekindDomain R] [IsFractionRing R K]

theorem GlobalTheory.MaxLatStruct.mem_of_int (hσ : ∀ r, algebraMap R K (σ r) = star (algebraMap R K r)) (hs : h.IsSymm)
    (hM : IsMaxLat h M) {y : V} (hy : y ∈ dual h M) (hyy : h y y ∈ (1 : Submodule R K)) : y ∈ M := by sorry
