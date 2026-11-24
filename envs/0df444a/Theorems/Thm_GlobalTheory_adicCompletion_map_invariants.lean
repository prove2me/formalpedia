-- Prove2me | Theorems.Thm_GlobalTheory_adicCompletion_map_invariants
-- name    : GlobalTheory.adicCompletion_map_invariants
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:06:16.373149+00:00
-- url     : https://prove2.me/theorems/10f9da0e-e821-44cf-942f-db4f411fe944
-- title:
--   Global Theory: adic Completion map invariants
-- statement:
--   The Global Theory construction uses the adic Completion map invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionMapInvariants.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionMapInvariants.lean#L8-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapSubApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionMapInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open AdicCompletion

theorem GlobalTheory.adicCompletion_map_invariants : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (N M : Type) [AddCommGroup N] [Module A N]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (f : N →ₗ[A] M) (Γ : Type) [Finite Γ] (g : Γ → (M →ₗ[A] M)),
    Function.Injective f → (∀ x, x ∈ LinearMap.range f ↔ ∀ σ, g σ x = x) →
    Function.Injective (AdicCompletion.map J f) ∧
      ∀ y, y ∈ LinearMap.range (AdicCompletion.map J f) ↔ ∀ σ, AdicCompletion.map J (g σ) y = y := by sorry
