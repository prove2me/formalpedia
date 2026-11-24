-- Prove2me | Theorems.Thm_GlobalTheory_Izumi_exists_dominating_eq_mul_of_not_mem_span
-- name    : GlobalTheory.Izumi.exists_dominating_eq_mul_of_not_mem_span
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:24:00.03259+00:00
-- url     : https://prove2.me/theorems/264ae151-d271-4eda-a810-a464eb93ed24
-- title:
--   Izumi: exists dominating eq mul of not mem span
-- statement:
--   The Izumi construction uses the exists dominating eq mul of not mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDominatingLocalDomainEqMulMaximal.lean#L70-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDominatingLocalDomainEqMulMaximal.lean#L70-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDominatingLocalDomainEqMulMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.Izumi

theorem GlobalTheory.Izumi.exists_dominating_eq_mul_of_not_mem_span :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
      [IsIntegrallyClosed R] (f G : R), G ∉ Ideal.span {f} →
      ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B) (_ : IsNoetherianRing B)
        (ι : R →+* B), Function.Injective ι ∧ IsLocalHom ι ∧
        (∀ b : B, ∃ r : R, b - ι r ∈ maximalIdeal B) ∧ ∃ u ∈ maximalIdeal B, ι f = ι G * u := by sorry
