-- Prove2me | Theorems.Thm_GlobalTheory_SA_mem_smulLat
-- name    : GlobalTheory.SA.mem_smulLat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:34:29.045032+00:00
-- url     : https://prove2.me/theorems/5035c9d1-f65d-4931-950d-b445eeca2833
-- title:
--   SA: mem smul Lat
-- statement:
--   The SA construction uses the mem smul Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/SymmetricFlagBasisVectorsApplyCentre.lean#L156-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/SymmetricFlagBasisVectorsApplyCentre.lean#L156-L157

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SA
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}
omit [IsScalarTower R K V] [Algebra R K] [StarRing K] [Field K] [Module K V]

theorem GlobalTheory.SA.mem_smulLat (g : R) (Λ : Submodule R V) (x : V) : x ∈ smulLat g Λ ↔ ∃ y ∈ Λ, g • y = x := by sorry
