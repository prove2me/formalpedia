-- Prove2me | Theorems.Thm_GlobalTheory_mem_sq_localization_of_pderiv_mem
-- name    : GlobalTheory.mem_sq_localization_of_pderiv_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:10:58.38167+00:00
-- url     : https://prove2.me/theorems/d74ab511-4994-490a-9ba3-e5e2646bf9f6
-- title:
--   Global Theory: mem sq localization of pderiv mem
-- statement:
--   The Global Theory construction uses the mem sq localization of pderiv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSqLocalizationOfPderivMem.lean#L21-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSqLocalizationOfPderivMem.lean#L21-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSqLocalizationOfPderivMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.mem_sq_localization_of_pderiv_mem :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) → ∀ x ∈ Q, (∀ s, MvPolynomial.pderiv s x ∈ Q) → ∃ g, g ∉ Q ∧ g * x ∈ Q ^ 2 := by sorry
