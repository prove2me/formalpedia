-- Prove2me | Theorems.Thm_GlobalTheory_Chevalley_exists_le_sup_maximalIdeal_pow_of_antitone
-- name    : GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:31.88087+00:00
-- url     : https://prove2.me/theorems/67b389d0-458b-572a-b9d3-719f177c997f
-- title:
--   Chevalley: exists le sup maximal Ideal pow of antitone
-- statement:
--   The Chevalley construction uses the exists le sup maximal Ideal pow of antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChevalleyExistsLeSupMaximalIdealPowOfAntitone.lean#L23-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChevalleyExistsLeSupMaximalIdealPowOfAntitone.lean#L23-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLeMaximalIdealPowSmulOfDirected
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChevalleyExistsLeSupMaximalIdealPowOfAntitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.Chevalley

theorem GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : ℕ → Ideal A) (J : Ideal A),
      Antitone K → (∀ e, maximalIdeal A ^ e ≤ K e) →
      (∀ (F : AdicCompletion (maximalIdeal A) A) (a : ℕ → A),
        (∀ n, F - algebraMap A (AdicCompletion (maximalIdeal A) A) (a n) ∈
          maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) →
        (∀ n, a n ∈ K n) → F ∈ J.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) →
      ∀ k : ℕ, ∃ e : ℕ, K e ≤ J ⊔ maximalIdeal A ^ k := by sorry
