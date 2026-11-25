-- Prove2me | Theorems.Thm_GlobalTheory_MaxLatStruct_mem_of_local
-- name    : GlobalTheory.MaxLatStruct.mem_of_local
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:54:00.439158+00:00
-- url     : https://prove2.me/theorems/b00a25c5-a9b9-47da-928d-f0e10adf623a
-- title:
--   Max Lat Struct: mem of local
-- statement:
--   The Max Lat Struct construction uses the mem of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L220-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L220-L229

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
omit [IsDedekindDomain R]

theorem GlobalTheory.MaxLatStruct.mem_of_local (L : Submodule R V) (x : V)
    (hx : ∀ Q : Ideal R, Q.IsMaximal → ∃ s ∉ Q, s • x ∈ L) : x ∈ L := by sorry
