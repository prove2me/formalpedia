-- Prove2me | Theorems.Thm_GlobalTheory_T_alternating_form_lattice_integrality
-- name    : GlobalTheory.T.alternating_form_lattice_integrality
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:15.254124+00:00
-- url     : https://prove2.me/theorems/612e46f7-cf5f-5836-b5e2-e5452bef6a06
-- title:
--   T: alternating form lattice integrality
-- statement:
--   The T construction uses the alternating form lattice integrality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AlternatingFormLatticeIntegralityStatement.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AlternatingFormLatticeIntegralityStatement.lean#L7-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlternatingFormLatticeIntegrality
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlternatingFormLatticeIntegralityStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.alternating_form_lattice_integrality : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (L : Set V),
    (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) → ∀ (P : V → V → F),
    (∀ x ∈ L, ∀ x' ∈ L, P x x' = -P x' x) →
    (∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, P (x₁ + x₂) x' = P x₁ x' + P x₂ x') →
    (∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, P ((a : F) • x) x' = (a : F) * P x x') →
    ∀ {x x' : V}, x ∈ L → x' ∈ L → P x x' ≠ 0 →
    ∃ B : LinearMap.BilinForm F V, (∀ z, B z z = 0) ∧ ∀ z ∈ L, ∀ w ∈ L, P z w = B z w := by sorry
