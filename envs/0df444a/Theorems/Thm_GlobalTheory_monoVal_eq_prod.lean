-- Prove2me | Theorems.Thm_GlobalTheory_monoVal_eq_prod
-- name    : GlobalTheory.monoVal_eq_prod
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:14.832205+00:00
-- url     : https://prove2.me/theorems/4c8e0cc7-a852-4e21-96cc-dca83cc59181
-- title:
--   Global Theory: mono Val eq prod
-- statement:
--   The Global Theory construction uses the mono Val eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L37-L39

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

theorem GlobalTheory.monoVal_eq_prod [CommMonoid R] [Fintype ι] (f : ι → R) (α : ι →₀ ℕ) :
    monoVal f α = ∏ i, f i ^ α i := by sorry
