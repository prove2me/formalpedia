-- Prove2me | Theorems.Thm_GlobalTheory_gl_hom_nnreal_trivial_of_scalar
-- name    : GlobalTheory.gl_hom_nnreal_trivial_of_scalar
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:13.537491+00:00
-- url     : https://prove2.me/theorems/88cbc38b-9ad6-437c-8efc-ab092e74c24d
-- title:
--   Global Theory: gl hom nnreal trivial of scalar
-- statement:
--   The Global Theory construction uses the gl hom nnreal trivial of scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/GlHomNnrealTrivialOfScalarTrivial.lean#L167-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/GlHomNnrealTrivialOfScalarTrivial.lean#L167-L185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_GlHomNnrealTrivialOfScalarTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
variable {k : Type} [Field k] {N : ℕ}

theorem GlobalTheory.gl_hom_nnreal_trivial_of_scalar :
    ∀ (k : Type) [Field k], (∃ x : k, x ≠ 0 ∧ x ≠ 1) → ∀ (N : ℕ) (φ : GL (Fin N) k →* NNReal),
      (∀ z : kˣ, φ (Matrix.GeneralLinearGroup.scalar (Fin N) z) = 1) → ∀ g, φ g = 1 := by sorry
