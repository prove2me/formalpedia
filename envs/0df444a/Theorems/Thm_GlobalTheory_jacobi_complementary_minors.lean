-- Prove2me | Theorems.Thm_GlobalTheory_jacobi_complementary_minors
-- name    : GlobalTheory.jacobi_complementary_minors
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:02:39.448329+00:00
-- url     : https://prove2.me/theorems/657089c1-afbc-407e-9bdb-95974eb56a95
-- title:
--   Global Theory: jacobi complementary minors
-- statement:
--   The Global Theory construction uses the jacobi complementary minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PluckerMinorsProportional.lean#L23-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PluckerMinorsProportional.lean#L23-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PluckerMinorsProportional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.jacobi_complementary_minors {K : Type} [Field K] {p q : ℕ}
    (α : Matrix (Fin p) (Fin p ⊕ Fin q) K) (β : Matrix (Fin q) (Fin p ⊕ Fin q) K)
    (hαβ : α * β.transpose = 0)
    (h₀ : ∃ π₀ : Equiv.Perm (Fin p ⊕ Fin q), (α.submatrix id (π₀ ∘ Sum.inl)).det ≠ 0)
    (h₁ : ∃ π₁ : Equiv.Perm (Fin p ⊕ Fin q), (β.submatrix id (π₁ ∘ Sum.inr)).det ≠ 0) :
    ∃ lam : K, ∀ π : Equiv.Perm (Fin p ⊕ Fin q),
      ((Equiv.Perm.sign π : ℤ) : K) * (α.submatrix id (π ∘ Sum.inl)).det =
        lam * (β.submatrix id (π ∘ Sum.inr)).det := by sorry
