-- Prove2me | Theorems.Thm_GlobalTheory_alternating_sub_mem_smul_top
-- name    : GlobalTheory.alternating_sub_mem_smul_top
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:47.284165+00:00
-- url     : https://prove2.me/theorems/05026ce0-02ab-4790-9eda-323f9743b8bd
-- title:
--   Global Theory: alternating sub mem smul top
-- statement:
--   The Global Theory construction uses the alternating sub mem smul top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L100-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L100-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  {D : ℕ}

theorem GlobalTheory.alternating_sub_mem_smul_top (ω : M [⋀^Fin D]→ₗ[A] N) (I : Ideal A) (v w : Fin D → M)
    (hvw : ∀ k, v k - w k ∈ I • (⊤ : Submodule A M)) :
    ω v - ω w ∈ I • (⊤ : Submodule A N) := by sorry
