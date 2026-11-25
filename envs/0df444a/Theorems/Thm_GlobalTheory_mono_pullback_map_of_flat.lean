-- Prove2me | Theorems.Thm_GlobalTheory_mono_pullback_map_of_flat
-- name    : GlobalTheory.mono_pullback_map_of_flat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:53:57.26785+00:00
-- url     : https://prove2.me/theorems/b973467b-da2e-4648-a6e5-b8aae7cc38a4
-- title:
--   Global Theory: mono pullback map of flat
-- statement:
--   The Global Theory construction uses the mono pullback map of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MonoPullbackMapOfFlat.lean#L206-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MonoPullbackMapOfFlat.lean#L206-L231

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MonoPullbackMapOfFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory.SkyMod

theorem GlobalTheory.mono_pullback_map_of_flat : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [Flat f] (G G' : Y.Modules)
    (φ : G ⟶ G') [Mono φ], Mono ((Scheme.Modules.pullback f).map φ) := by sorry
