-- Prove2me | Theorems.Thm_GlobalTheory_powGr_map_comp
-- name    : GlobalTheory.powGr.map_comp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:24:39.380805+00:00
-- url     : https://prove2.me/theorems/171c4a68-691b-4068-9a94-ace77c25e3a3
-- title:
--   pow Gr: map comp
-- statement:
--   The pow Gr construction uses the map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L191-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L191-L195

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
variable {R : Type*} [CommRing R]
open GlobalTheory.powGr
variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (a : ℕ)
variable {M}

theorem GlobalTheory.powGr.map_comp {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (g : M →ₗ[R] N) (h : N →ₗ[R] P) : map I a (h ∘ₗ g) = map I a h ∘ₗ map I a g := by sorry
