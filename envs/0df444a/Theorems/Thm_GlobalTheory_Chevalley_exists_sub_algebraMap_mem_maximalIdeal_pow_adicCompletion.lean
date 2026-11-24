-- Prove2me | Theorems.Thm_GlobalTheory_Chevalley_exists_sub_algebraMap_mem_maximalIdeal_pow_adicCompletion
-- name    : GlobalTheory.Chevalley.exists_sub_algebraMap_mem_maximalIdeal_pow_adicCompletion
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:10:31.108082+00:00
-- url     : https://prove2.me/theorems/85bfa191-869a-4d6e-9f48-5ace48f5cd34
-- title:
--   Chevalley: exists sub algebra Map mem maximal Ideal pow adic Completion
-- statement:
--   The Chevalley construction uses the exists sub algebra Map mem maximal Ideal pow adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChevalleyExistsLeSupMaximalIdealPowOfAntitone.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChevalleyExistsLeSupMaximalIdealPowOfAntitone.lean#L9-L21

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

theorem GlobalTheory.Chevalley.exists_sub_algebraMap_mem_maximalIdeal_pow_adicCompletion (A : Type) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (F : AdicCompletion (maximalIdeal A) A) (n : ℕ) :
    ∃ a : A, F - algebraMap A (AdicCompletion (maximalIdeal A) A) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n := by sorry
