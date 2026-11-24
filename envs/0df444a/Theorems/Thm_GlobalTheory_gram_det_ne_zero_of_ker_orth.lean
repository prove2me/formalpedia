-- Prove2me | Theorems.Thm_GlobalTheory_gram_det_ne_zero_of_ker_orth
-- name    : GlobalTheory.gram_det_ne_zero_of_ker_orth
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:54:03.401272+00:00
-- url     : https://prove2.me/theorems/e182138d-e303-4c93-82ac-e1057b9eee0f
-- title:
--   Global Theory: gram det ne zero of ker orth
-- statement:
--   The Global Theory construction uses the gram det ne zero of ker orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GramDetNeZeroOfKerOrth.lean#L4-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GramDetNeZeroOfKerOrth.lean#L4-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramDetNeZeroOfKerOrth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial

theorem GlobalTheory.gram_det_ne_zero_of_ker_orth {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K) (hli : LinearIndependent K u) (hsp : Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' A)) (horth : ∀ x z, A *ᵥ x = 0 → ∑ k, σ ((A *ᵥ z) k) * x k = 0) (hdec : ∀ v, ∃ z y, A *ᵥ y = 0 ∧ v = A *ᵥ z + y) : (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det ≠ 0 := by sorry
