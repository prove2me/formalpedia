-- Prove2me | Theorems.Thm_GlobalTheory_WeightedInverseBound_wls_fintype
-- name    : GlobalTheory.WeightedInverseBound.wls_fintype
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:03:54.3578+00:00
-- url     : https://prove2.me/theorems/afbe2023-fcde-4d49-825a-1eef7233d2d7
-- title:
--   Weighted Inverse Bound: wls fintype
-- statement:
--   The Weighted Inverse Bound construction uses the wls fintype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulInvMulPosSemidefUniformBound.lean#L10-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulInvMulPosSemidefUniformBound.lean#L10-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulInvMulPosSemidefUniformBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory
open GlobalTheory.WeightedInverseBound

theorem GlobalTheory.WeightedInverseBound.wls_fintype {ι : Type} [Fintype ι] [DecidableEq ι] {g : ℕ} (L : Matrix ι (Fin g) ℝ)
    (hL : L.rank = g) : ∃ K : ℝ, ∀ (D : ι → ℝ) (b : ι → ℝ), (∀ k, 0 < D k) →
      ‖((L.transpose * Matrix.diagonal D * L)⁻¹ * L.transpose * Matrix.diagonal D).mulVec b‖
        ≤ K * ‖b‖ := by sorry
