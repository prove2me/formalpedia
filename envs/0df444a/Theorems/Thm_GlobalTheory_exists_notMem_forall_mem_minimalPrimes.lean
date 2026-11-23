-- Prove2me | Theorems.Thm_GlobalTheory_exists_notMem_forall_mem_minimalPrimes
-- name    : GlobalTheory.exists_notMem_forall_mem_minimalPrimes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:43.17353+00:00
-- url     : https://prove2.me/theorems/4f9ce48e-bc39-42ff-9c73-0f2558a4debf
-- title:
--   Global Theory: exists not Mem forall mem minimal Primes
-- statement:
--   The Global Theory construction uses the exists not Mem forall mem minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L51-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L51-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
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
universe u

theorem GlobalTheory.exists_notMem_forall_mem_minimalPrimes {B : Type*} [CommRing B] [IsNoetherianRing B]
    (I p : Ideal B) [p.IsPrime] (hp : ∀ P ∈ I.minimalPrimes, P ≤ p → P = p) :
    ∃ s ∉ p, ∀ P ∈ I.minimalPrimes, P ≠ p → s ∈ P := by sorry
