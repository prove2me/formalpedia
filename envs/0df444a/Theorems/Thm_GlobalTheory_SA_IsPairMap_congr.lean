-- Prove2me | Theorems.Thm_GlobalTheory_SA_IsPairMap_congr
-- name    : GlobalTheory.SA.IsPairMap.congr
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:32:39.48377+00:00
-- url     : https://prove2.me/theorems/bae1fb28-b1e9-49f6-8667-90286c4a21c6
-- title:
--   Is Pair Map: congr
-- statement:
--   The Is Pair Map construction uses the congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/SymmetricFlagBasisVectorsApplyCentre.lean#L399-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/SymmetricFlagBasisVectorsApplyCentre.lean#L399-L412

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

theorem GlobalTheory.SA.IsPairMap.congr (h : IsPairMap F F' F'' Λ g β) {β₁ : V ≃ₗ[K] V}
    (h1 : F'.X.map (β₁ : V →ₗ[K] V) = F''.X) (h2 : (perp H F'.X).map (β₁ : V →ₗ[K] V) = perp H F''.X)
    (he : ∀ x ∈ perp H F'.X, β₁ x - β x ∈ F''.X) : IsPairMap F F' F'' Λ g β₁ := by sorry
