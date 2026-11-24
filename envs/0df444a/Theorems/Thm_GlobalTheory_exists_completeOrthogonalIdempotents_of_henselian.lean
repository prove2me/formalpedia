-- Prove2me | Theorems.Thm_GlobalTheory_exists_completeOrthogonalIdempotents_of_henselian
-- name    : GlobalTheory.exists_completeOrthogonalIdempotents_of_henselian
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:00.016777+00:00
-- url     : https://prove2.me/theorems/985b285f-f295-4d7c-9134-e1fbb82661ae
-- title:
--   Global Theory: exists complete Orthogonal Idempotents of henselian
-- statement:
--   The Global Theory construction uses the exists complete Orthogonal Idempotents of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L344-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L344-L366

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

theorem GlobalTheory.exists_completeOrthogonalIdempotents_of_henselian (R S : Type*) [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Fintype (MaximalSpectrum S)] :
    ∃ e : MaximalSpectrum S → S, CompleteOrthogonalIdempotents e ∧
      ∀ (q : MaximalSpectrum S) (n : Ideal S), n.IsMaximal → (e q ∉ n ↔ n = q.asIdeal) := by sorry
