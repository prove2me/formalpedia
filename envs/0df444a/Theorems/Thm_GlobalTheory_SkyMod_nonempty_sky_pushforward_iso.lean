-- Prove2me | Theorems.Thm_GlobalTheory_SkyMod_nonempty_sky_pushforward_iso
-- name    : GlobalTheory.SkyMod.nonempty_sky_pushforward_iso
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:49:50.748315+00:00
-- url     : https://prove2.me/theorems/554addd6-05a8-5b85-a408-f3f12d402458
-- title:
--   Sky Mod: nonempty sky pushforward iso
-- statement:
--   The Sky Mod construction uses the nonempty sky pushforward iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MonoPullbackMapOfFlat.lean#L192-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MonoPullbackMapOfFlat.lean#L192-L202

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

theorem GlobalTheory.SkyMod.nonempty_sky_pushforward_iso : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (x : X), Nonempty (GlobalTheory.SkyMod.skyFunctor x ⋙ Scheme.Modules.pushforward f ≅ ModuleCat.restrictScalars (f.stalkMap x).hom ⋙ GlobalTheory.SkyMod.skyFunctor (f x)) := by sorry
