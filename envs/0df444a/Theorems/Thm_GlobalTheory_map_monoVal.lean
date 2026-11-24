-- Prove2me | Theorems.Thm_GlobalTheory_map_monoVal
-- name    : GlobalTheory.map_monoVal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:09:51.11485+00:00
-- url     : https://prove2.me/theorems/e56f4c06-ac3e-4f2f-82d2-44217d16d04c
-- title:
--   Global Theory: map mono Val
-- statement:
--   The Global Theory construction uses the map mono Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L56-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} {ι : Type*}

theorem GlobalTheory.map_monoVal [CommMonoid R] {S F : Type*} [CommMonoid S] [FunLike F R S]
    [MonoidHomClass F R S] (φ : F) (f : ι → R) (α : ι →₀ ℕ) :
    φ (monoVal f α) = monoVal (fun i => φ (f i)) α := by sorry
