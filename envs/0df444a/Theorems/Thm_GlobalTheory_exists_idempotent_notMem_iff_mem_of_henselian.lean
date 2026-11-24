-- Prove2me | Theorems.Thm_GlobalTheory_exists_idempotent_notMem_iff_mem_of_henselian
-- name    : GlobalTheory.exists_idempotent_notMem_iff_mem_of_henselian
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:18.693798+00:00
-- url     : https://prove2.me/theorems/89e06ab6-7a3e-491f-8f49-2fbe76d46d56
-- title:
--   Global Theory: exists idempotent not Mem iff mem of henselian
-- statement:
--   The Global Theory construction uses the exists idempotent not Mem iff mem of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L179-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L179-L195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct

theorem GlobalTheory.exists_idempotent_notMem_iff_mem_of_henselian (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (T : Set (MaximalSpectrum S)) :
    ∃ e : S, IsIdempotentElem e ∧ ∀ n : MaximalSpectrum S, (e ∉ n.asIdeal ↔ n ∈ T) := by sorry
