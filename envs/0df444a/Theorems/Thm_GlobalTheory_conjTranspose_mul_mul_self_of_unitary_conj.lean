-- Prove2me | Theorems.Thm_GlobalTheory_conjTranspose_mul_mul_self_of_unitary_conj
-- name    : GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:29.458826+00:00
-- url     : https://prove2.me/theorems/b0baebe0-5f7a-4e38-b0fa-1d6fc6ab9b5b
-- title:
--   Global Theory: conj Transpose mul mul self of unitary conj
-- statement:
--   The Global Theory construction uses the conj Transpose mul mul self of unitary conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjTransposeMulMulSelfOfUnitaryConj.lean#L10-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjTransposeMulMulSelfOfUnitaryConj.lean#L10-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjTransposeMulMulSelfOfUnitaryConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder
open Matrix
open GlobalTheory
open scoped ComplexOrder
open Matrix

theorem GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj :
    ∀ (n d : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ) (Xb Yb : Matrix (Fin n) (Fin d) ℂ) (y₀ : GL (Fin d) ℂ),
    J.conjTranspose = J → P.conjTranspose = P → Xb.conjTranspose * J * Xb = 0 → Yb.conjTranspose * J * Yb = 0 →
    Xb.conjTranspose * J * Yb = 1 →
    P * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) → P * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) →
    ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
      let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
      let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
      G.conjTranspose * P * G = P := by sorry
