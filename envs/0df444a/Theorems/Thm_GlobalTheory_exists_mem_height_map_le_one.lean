-- Prove2me | Theorems.Thm_GlobalTheory_exists_mem_height_map_le_one
-- name    : GlobalTheory.exists_mem_height_map_le_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:09.080136+00:00
-- url     : https://prove2.me/theorems/b45b79a3-03a1-4b30-bde8-5aa890574109
-- title:
--   Global Theory: exists mem height map le one
-- statement:
--   The Global Theory construction uses the exists mem height map le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L154-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L154-L185

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

theorem GlobalTheory.exists_mem_height_map_le_one {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : Ideal A) [m.IsPrime] {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (h : ∃ p ∈ U, p.asIdeal ≤ m) :
    ∃ q ∈ U, q.asIdeal ≤ m ∧ (m.map (Ideal.Quotient.mk q.asIdeal)).height ≤ 1 := by sorry
