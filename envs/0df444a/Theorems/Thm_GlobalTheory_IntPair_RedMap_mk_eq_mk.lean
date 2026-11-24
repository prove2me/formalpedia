-- Prove2me | Theorems.Thm_GlobalTheory_IntPair_RedMap_mk_eq_mk
-- name    : GlobalTheory.IntPair.RedMap.mk_eq_mk
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:08:04.618218+00:00
-- url     : https://prove2.me/theorems/00911cfd-733b-4be1-ace9-95b945017495
-- title:
--   Red Map: mk eq mk
-- statement:
--   The Red Map construction uses the mk eq mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/SameRedEquivalence.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/SameRedEquivalence.lean#L55-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FinrankLeFinrankInfPerpXPlus
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_SameRedEquivalence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IntPair
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA Module
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}
variable {F F' F'' F₁ G' G'' : FlagD H r} {Λ Λ₁ : Submodule R V} {g : R} {β β₁ s s₁ s₂ : V ≃ₗ[K] V}
open GlobalTheory.IntPair.RedMap

theorem GlobalTheory.IntPair.RedMap.mk_eq_mk (h : IsPairMap F F' F'' Λ g β) (h₁ : IsPairMap F F' F'' Λ g β₁) :
    mk β h = mk β₁ h₁ ↔ SameRed F' F'' β β₁ := by sorry
