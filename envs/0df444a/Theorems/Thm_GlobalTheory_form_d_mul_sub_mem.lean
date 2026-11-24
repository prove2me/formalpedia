-- Prove2me | Theorems.Thm_GlobalTheory_form_d_mul_sub_mem
-- name    : GlobalTheory.form_d_mul_sub_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:51:49.96224+00:00
-- url     : https://prove2.me/theorems/29cffde1-4138-4c7a-9a2c-4587583001fd
-- title:
--   Global Theory: form d mul sub mem
-- statement:
--   The Global Theory construction uses the form d mul sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L148-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L148-L156

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
variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [AddCommGroup N] [Module A N] {D : ℕ}
variable (d : Derivation R A M) (ω : M [⋀^Fin D]→ₗ[A] N)

theorem GlobalTheory.form_d_mul_sub_mem (I : Ideal A) (h : A) (g : Fin D → A) (hg : ∀ k, g k ∈ I) :
    ω (fun k => d (h * g k)) - h ^ D • ω (fun k => d (g k)) ∈ I • (⊤ : Submodule A N) := by sorry
