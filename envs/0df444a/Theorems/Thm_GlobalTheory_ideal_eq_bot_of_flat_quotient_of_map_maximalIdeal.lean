-- Prove2me | Theorems.Thm_GlobalTheory_ideal_eq_bot_of_flat_quotient_of_map_maximalIdeal
-- name    : GlobalTheory.ideal_eq_bot_of_flat_quotient_of_map_maximalIdeal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:47:09.55527+00:00
-- url     : https://prove2.me/theorems/a34a878f-fd09-411c-9040-4b7749f38e64
-- title:
--   Global Theory: ideal eq bot of flat quotient of map maximal Ideal
-- statement:
--   The Global Theory construction uses the ideal eq bot of flat quotient of map maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L536-L541
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L536-L541

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing

theorem GlobalTheory.ideal_eq_bot_of_flat_quotient_of_map_maximalIdeal (T : Type*) {R : Type*} [CommRing T]
    [IsDomain T] [IsDiscreteValuationRing T] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra T R] (h : (maximalIdeal T).map (algebraMap T R) = maximalIdeal R) {J : Ideal R}
    (hJ : J ≠ ⊤) [Module.Flat T (R ⧸ J)] : J = ⊥ := by sorry
