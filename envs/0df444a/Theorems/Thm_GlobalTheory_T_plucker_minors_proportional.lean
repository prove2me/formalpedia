-- Prove2me | Theorems.Thm_GlobalTheory_T_plucker_minors_proportional
-- name    : GlobalTheory.T.plucker_minors_proportional
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:13.524195+00:00
-- url     : https://prove2.me/theorems/4af019f4-fbae-40ca-b330-95868f3c69b7
-- title:
--   T: plucker minors proportional
-- statement:
--   The T construction uses the plucker minors proportional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PluckerMinorsProportionalStatement.lean#L5-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PluckerMinorsProportionalStatement.lean#L5-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PluckerMinorsProportional
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PluckerMinorsProportionalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.plucker_minors_proportional : ∀ {K : Type} [Field K] {p q : ℕ} (α : Matrix (Fin p) (Fin p ⊕ Fin q) K) (β : Matrix (Fin q) (Fin p ⊕ Fin q) K),
  α * β.transpose = 0 →
  (∃ π₀ : Equiv.Perm (Fin p ⊕ Fin q), (α.submatrix id (π₀ ∘ Sum.inl)).det ≠ 0) →
  (∃ π₁ : Equiv.Perm (Fin p ⊕ Fin q), (β.submatrix id (π₁ ∘ Sum.inr)).det ≠ 0) →
  ∃ lam : K, ∀ π : Equiv.Perm (Fin p ⊕ Fin q),
    ((Equiv.Perm.sign π : ℤ) : K) * (α.submatrix id (π ∘ Sum.inl)).det = lam * (β.submatrix id (π ∘ Sum.inr)).det := by sorry
