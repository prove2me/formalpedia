-- Prove2me | Theorems.Thm_GlobalTheory_isUnit_monoVal
-- name    : GlobalTheory.isUnit_monoVal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:01:16.219498+00:00
-- url     : https://prove2.me/theorems/9ef83f45-b961-45d1-a9cd-8de240b2e104
-- title:
--   Global Theory: is Unit mono Val
-- statement:
--   The Global Theory construction uses the is Unit mono Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L61-L63

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

theorem GlobalTheory.isUnit_monoVal [CommMonoid R] {u : ι → R} (hu : ∀ i, IsUnit (u i)) (α : ι →₀ ℕ) :
    IsUnit (monoVal u α) := by sorry
