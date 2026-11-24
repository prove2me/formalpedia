-- Prove2me | Theorems.Thm_GlobalTheory_SA_isPairMap_of_aut
-- name    : GlobalTheory.SA.isPairMap_of_aut
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:34:24.338881+00:00
-- url     : https://prove2.me/theorems/16d3ad5f-ebbb-4b27-bc32-7907b7f2893f
-- title:
--   SA: is Pair Map of aut
-- statement:
--   The SA construction uses the is Pair Map of aut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/SymmetricFlagBasisVectorsApplyCentre.lean#L414-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/SymmetricFlagBasisVectorsApplyCentre.lean#L414-L431

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

theorem GlobalTheory.SA.isPairMap_of_aut (hc : IsCong F F'' Λ g) (hβ : β ∈ isomGrp H) (hΛ : imLat β Λ = Λ)
    (hX : F'.X.map (β : V →ₗ[K] V) = F''.X) (hz : β F'.z - F''.z ∈ F''.X)
    (hι : ∀ l' ∈ Λ ⊓ rs R (perp H F'.X), β l' - l' ∈ latX F Λ ⊔ smulLat g Λ) :
    IsPairMap F F' F'' Λ g β := by sorry
