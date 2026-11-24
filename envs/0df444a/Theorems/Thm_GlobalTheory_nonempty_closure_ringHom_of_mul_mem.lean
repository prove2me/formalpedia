-- Prove2me | Theorems.Thm_GlobalTheory_nonempty_closure_ringHom_of_mul_mem
-- name    : GlobalTheory.nonempty_closure_ringHom_of_mul_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:12:44.155799+00:00
-- url     : https://prove2.me/theorems/608b6425-ad90-42ed-9073-f199859b27e8
-- title:
--   Global Theory: nonempty closure ring Hom of mul mem
-- statement:
--   The Global Theory construction uses the nonempty closure ring Hom of mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NumberFieldToModPSquared.lean#L66-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NumberFieldToModPSquared.lean#L66-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepIntPolyRootModPrimeSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NumberFieldToModPSquared
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory

theorem GlobalTheory.nonempty_closure_ringHom_of_mul_mem : ∀ (K : Type) [Field K] [CharZero K] (O : Subring K) (R : Type) [CommRing R] (ψ : O →+* R) (N : ℕ), 0 < N → IsUnit (N : R) → ∀ (S : Finset K), (∀ s ∈ S, (N : K) * s ∈ O) → Nonempty (Subring.closure (S : Set K) →+* R) := by sorry
