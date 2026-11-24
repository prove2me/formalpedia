-- Prove2me | Theorems.Thm_GlobalTheory_exists_diagonal_operator_killing
-- name    : GlobalTheory.exists_diagonal_operator_killing
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:31:20.080857+00:00
-- url     : https://prove2.me/theorems/204a52c4-7544-49ca-a214-15eb0f4d3a7b
-- title:
--   Global Theory: exists diagonal operator killing
-- statement:
--   The Global Theory construction uses the exists diagonal operator killing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SimultaneousEigenbasisIntegral.lean#L5-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SimultaneousEigenbasisIntegral.lean#L5-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SimultaneousEigenbasisIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_diagonal_operator_killing (R : Subring ℂ) {g : ℕ} {V : Type} [AddCommGroup V]
    [Module R V] (ψ : V →ₗ[R] (Fin g → ℂ)) {J : Type} (T : J → V →ₗ[R] V) (lam : J → Fin g → ℂ)
    (hT : ∀ a v j, ψ (T a v) j = lam a j * ψ v j)
    (hsep : ∀ j k, j ≠ k → ∃ a, lam a j ≠ lam a k)
    (hK : ∀ a j, ∃ x ∈ R, ∃ y ∈ R, y ≠ 0 ∧ lam a j * y = x) (i : Fin g) (s : Finset (Fin g))
    (hi : i ∉ s) :
    ∃ (P : V →ₗ[R] V) (C : Fin g → ℂ), C i ≠ 0 ∧ (∀ k ∈ s, C k = 0) ∧
      ∀ v k, ψ (P v) k = C k * ψ v k := by sorry
