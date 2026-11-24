-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_of_forall_mem_discreteValuationSubring
-- name    : GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:57:19.383879+00:00
-- url     : https://prove2.me/theorems/8f16ceed-caa1-41f1-92c4-f09f39034d44
-- title:
--   Global Theory: is Integral of forall mem discrete Valuation Subring
-- statement:
--   The Global Theory construction uses the is Integral of forall mem discrete Valuation Subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegralOfForallMemDiscreteValuationSubring.lean#L8-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegralOfForallMemDiscreteValuationSubring.lean#L8-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegralOfForallMemDiscreteValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring : ∀ (S K : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field K] [Algebra S K] [IsFractionRing S K] (t : K), (∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ s : S, algebraMap S K s ∈ V) → t ∈ V) → IsIntegral S t := by sorry
