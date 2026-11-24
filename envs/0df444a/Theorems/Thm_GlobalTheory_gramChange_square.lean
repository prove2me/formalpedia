-- Prove2me | Theorems.Thm_GlobalTheory_gramChange_square
-- name    : GlobalTheory.gramChange_square
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:14.327104+00:00
-- url     : https://prove2.me/theorems/de319b8f-2554-4b65-b6c2-d8c25f5efd04
-- title:
--   Global Theory: gram Change square
-- statement:
--   The Global Theory construction uses the gram Change square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GramDetChangeOfBases.lean#L12-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GramDetChangeOfBases.lean#L12-L47

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

theorem GlobalTheory.gramChange_square {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {ι : Type}
    [Fintype ι] [DecidableEq ι] (u v : ι → Fin n → K) (hu : LinearIndependent K u)
    (hv : LinearIndependent K v) (hvu : ∀ i, v i ∈ Submodule.span K (Set.range u)) :
    ∃ d : K, d ≠ 0 ∧ (Matrix.of fun i j => ∑ k, σ (v i k) * v j k).det
      = σ d * d * (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det := by sorry
