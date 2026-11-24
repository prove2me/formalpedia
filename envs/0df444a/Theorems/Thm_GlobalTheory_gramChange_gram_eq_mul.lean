-- Prove2me | Theorems.Thm_GlobalTheory_gramChange_gram_eq_mul
-- name    : GlobalTheory.gramChange_gram_eq_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:02.284108+00:00
-- url     : https://prove2.me/theorems/a4394408-c247-444b-bb1f-347d58e516fa
-- title:
--   Global Theory: gram Change gram eq mul
-- statement:
--   The Global Theory construction uses the gram Change gram eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GramDetChangeOfBases.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GramDetChangeOfBases.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramDetChangeOfBases
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory

theorem GlobalTheory.gramChange_gram_eq_mul {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {ι : Type} [Fintype ι]
    (u : ι → Fin n → K) :
    (Matrix.of fun i j => ∑ k, σ (u i k) * u j k) = (Matrix.of u).map σ * (Matrix.of u)ᵀ := by sorry
