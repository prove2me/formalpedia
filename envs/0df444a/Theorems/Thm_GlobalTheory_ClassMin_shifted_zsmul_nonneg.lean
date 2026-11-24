-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_shifted_zsmul_nonneg
-- name    : GlobalTheory.ClassMin.shifted_zsmul_nonneg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:13:52.604827+00:00
-- url     : https://prove2.me/theorems/06341b0f-ba6f-46df-9e94-72e8c4490184
-- title:
--   Class Min: shifted zsmul nonneg
-- statement:
--   The Class Min construction uses the shifted zsmul nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsShiftedLtClassMin.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsShiftedLtClassMin.lean#L33-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsShiftedLtClassMin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Module
open scoped Pointwise
variable {X : Type*} [AddCommGroup X]
variable {Q : QuadraticMap ℤ X ℝ} {N : ℤ}

theorem GlobalTheory.ClassMin.shifted_zsmul_nonneg (hN : 0 < N) {ν : X →+ ℝ} (h : ∀ μ, 0 ≤ Q μ + ν μ) (μ : X) :
    0 ≤ Q (N • μ) / N + ν (N • μ) := by sorry
