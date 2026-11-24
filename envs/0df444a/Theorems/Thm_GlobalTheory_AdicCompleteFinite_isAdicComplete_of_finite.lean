-- Prove2me | Theorems.Thm_GlobalTheory_AdicCompleteFinite_isAdicComplete_of_finite
-- name    : GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:55:10.201+00:00
-- url     : https://prove2.me/theorems/0b2df6c4-d223-40ce-8d8b-a53c81b466a7
-- title:
--   Adic Complete Finite: is Adic Complete of finite
-- statement:
--   The Adic Complete Finite construction uses the is Adic Complete of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAdicCompleteOfFinite.lean#L40-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAdicCompleteOfFinite.lean#L40-L65

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

theorem GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite (R S : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [CommRing S] [IsLocalRing S] [Algebra R S]
    [Module.Finite R S] : IsAdicComplete (IsLocalRing.maximalIdeal S) S := by sorry
