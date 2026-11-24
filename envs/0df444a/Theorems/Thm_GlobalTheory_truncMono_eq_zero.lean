-- Prove2me | Theorems.Thm_GlobalTheory_truncMono_eq_zero
-- name    : GlobalTheory.truncMono_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:23:58.282013+00:00
-- url     : https://prove2.me/theorems/63edd24e-6df4-4241-9bee-2987bd85883a
-- title:
--   Global Theory: trunc Mono eq zero
-- statement:
--   The Global Theory construction uses the trunc Mono eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedMonomialsLinearIndependentOverConstants.lean#L26-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TruncatedMonomialsLinearIndependentOverConstants.lean#L26-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedMonomialsLinearIndependentOverConstants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open MvPolynomial

theorem GlobalTheory.truncMono_eq_zero {p : ℕ} [Fact p.Prime] {k A : Type} [Field k] [CommRing A]
    [Algebra k A] [CharP k p] {d : ℕ}
    (x : Fin d → A) (E : Fin d → Derivation k A A)
    (hE : ∀ i j, E i (x j) = if i = j then 1 else 0) (B : Subalgebra k A)
    (hB : ∀ i, ∀ b ∈ B, E i b = 0) :
    ∀ n : ℕ, ∀ F : MvPolynomial (Fin d) B,
      (∀ m ∈ F.support, (∀ i, m i < p) ∧ ∑ i, m i ≤ n) → aeval x F = 0 → F = 0 := by sorry
