-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_injective_adicCompletion_map_of_finite
-- name    : GlobalTheory.T.exists_injective_adicCompletion_map_of_finite
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:35:58.107273+00:00
-- url     : https://prove2.me/theorems/cbcef8da-9973-496d-884f-e993502669f8
-- title:
--   T: exists injective adic Completion map of finite
-- statement:
--   The T construction uses the exists injective adic Completion map of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsInjectiveAdicCompletionMapOfFiniteStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsInjectiveAdicCompletionMapOfFiniteStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsInjectiveAdicCompletionMapOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsInjectiveAdicCompletionMapOfFiniteStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_injective_adicCompletion_map_of_finite : ∀ (D N : Type) [CommRing D] [CommRing N] [IsNoetherianRing D] [Algebra D N] [Module.Finite D N], Function.Injective (algebraMap D N) → ∀ J : Ideal D, ∃ f : AdicCompletion J D →+* AdicCompletion (J.map (algebraMap D N)) N, Function.Injective f := by sorry
