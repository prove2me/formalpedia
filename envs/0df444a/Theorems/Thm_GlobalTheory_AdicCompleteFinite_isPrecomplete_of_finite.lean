-- Prove2me | Theorems.Thm_GlobalTheory_AdicCompleteFinite_isPrecomplete_of_finite
-- name    : GlobalTheory.AdicCompleteFinite.isPrecomplete_of_finite
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:55:30.684636+00:00
-- url     : https://prove2.me/theorems/5baa7905-db67-4912-b740-7a078c196f3c
-- title:
--   Adic Complete Finite: is Precomplete of finite
-- statement:
--   The Adic Complete Finite construction uses the is Precomplete of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAdicCompleteOfFinite.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAdicCompleteOfFinite.lean#L7-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsAdicCompleteOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.AdicCompleteFinite

theorem GlobalTheory.AdicCompleteFinite.isPrecomplete_of_finite {R M : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by sorry
