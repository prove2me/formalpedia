-- Prove2me | Theorems.Thm_GlobalTheory_T_adicCompletion_map_injective_and_invariants
-- name    : GlobalTheory.T.adicCompletion_map_injective_and_invariants
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:49.683321+00:00
-- url     : https://prove2.me/theorems/907c4640-16d6-4dbd-8c8f-68319ebde200
-- title:
--   T: adic Completion map injective and invariants
-- statement:
--   The T construction uses the adic Completion map injective and invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionMapInvariantsStatement.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCompletionMapInvariantsStatement.lean#L5-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionMapInvariants
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCompletionMapInvariantsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.adicCompletion_map_injective_and_invariants : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (N M : Type) [AddCommGroup N] [Module A N]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (f : N →ₗ[A] M) (Γ : Type) [Finite Γ] (g : Γ → (M →ₗ[A] M)),
    Function.Injective f → (∀ x, x ∈ LinearMap.range f ↔ ∀ σ, g σ x = x) →
    Function.Injective (AdicCompletion.map J f) ∧
      ∀ y, y ∈ LinearMap.range (AdicCompletion.map J f) ↔ ∀ σ, AdicCompletion.map J (g σ) y = y := by sorry
