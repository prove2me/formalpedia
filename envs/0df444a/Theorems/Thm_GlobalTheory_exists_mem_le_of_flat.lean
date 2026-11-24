-- Prove2me | Theorems.Thm_GlobalTheory_exists_mem_le_of_flat
-- name    : GlobalTheory.exists_mem_le_of_flat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:24.579796+00:00
-- url     : https://prove2.me/theorems/3a8a53fe-9609-4340-8906-1b0740561cb3
-- title:
--   Global Theory: exists mem le of flat
-- statement:
--   The Global Theory construction uses the exists mem le of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L235-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L235-L258

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

theorem GlobalTheory.exists_mem_le_of_flat {O A : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [IsNoetherianRing A] [Algebra O A] [Module.Flat O A]
    (m : Ideal A) [m.IsPrime] {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (hd : ∀ p : PrimeSpectrum A, p.asIdeal.comap (algebraMap O A) ≠ maximalIdeal O →
      p ∈ closure U) :
    ∃ p ∈ U, p.asIdeal ≤ m ∧ p.asIdeal.comap (algebraMap O A) ≠ maximalIdeal O := by sorry
