-- Prove2me | Theorems.Thm_GlobalTheory_SA_isPairMap_refl
-- name    : GlobalTheory.SA.isPairMap_refl
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:36:04.905302+00:00
-- url     : https://prove2.me/theorems/fd01aa6d-a6e5-4efd-b841-b4eb3e66ab59
-- title:
--   SA: is Pair Map refl
-- statement:
--   The SA construction uses the is Pair Map refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/SymmetricFlagBasisVectorsApplyCentre.lean#L433-L435
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/SymmetricFlagBasisVectorsApplyCentre.lean#L433-L435

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
variable {F F' F'' : FlagD H r} {Λ : Submodule R V} {g : R} {β : V ≃ₗ[K] V}

theorem GlobalTheory.SA.isPairMap_refl (hc : IsCong F F' Λ g) : IsPairMap F F' F' Λ g (LinearEquiv.refl K V) := by sorry
