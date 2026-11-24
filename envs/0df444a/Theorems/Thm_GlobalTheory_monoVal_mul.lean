-- Prove2me | Theorems.Thm_GlobalTheory_monoVal_mul
-- name    : GlobalTheory.monoVal_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:12:56.309596+00:00
-- url     : https://prove2.me/theorems/76a05d90-52dc-42e3-a577-2cdf948a7538
-- title:
--   Global Theory: mono Val mul
-- statement:
--   The Global Theory construction uses the mono Val mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L52-L54

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

theorem GlobalTheory.monoVal_mul [CommMonoid R] (f g : ι → R) (α : ι →₀ ℕ) :
    monoVal (fun i => f i * g i) α = monoVal f α * monoVal g α := by sorry
