-- Prove2me | Theorems.Thm_GlobalTheory_eq_of_perm_inv_invariant_of_multiset_eq
-- name    : GlobalTheory.eq_of_perm_inv_invariant_of_multiset_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:41.832375+00:00
-- url     : https://prove2.me/theorems/a2bd8614-eb76-4463-95ea-549cf66b2128
-- title:
--   Global Theory: eq of perm inv invariant of multiset eq
-- statement:
--   The Global Theory construction uses the eq of perm inv invariant of multiset eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SymmetricFunctionInverseInvariant.lean#L19-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SymmetricFunctionInverseInvariant.lean#L19-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymmetricFunctionInverseInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.eq_of_perm_inv_invariant_of_multiset_eq :
    ∀ (m : ℕ) (f : (Fin m → ℂ) → ℂ), (∀ α : Fin m → ℂ, (∀ i, α i ≠ 0) → (∀ π : Equiv.Perm (Fin m), f (α ∘ π) = f α) ∧ ∀ i, f (Function.update α i (α i)⁻¹) = f α) → ∀ α α' : Fin m → ℂ, (∀ i, α i ≠ 0) → Finset.univ.val.map α + Finset.univ.val.map (fun i => (α i)⁻¹) = Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹) → f α = f α' := by sorry
