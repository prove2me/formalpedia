-- Prove2me | Theorems.Thm_GlobalTheory_PointStepCompare_posDef_of_int
-- name    : GlobalTheory.PointStepCompare.posDef_of_int
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:50:25.382679+00:00
-- url     : https://prove2.me/theorems/f5bd804b-7222-4bb8-a14f-efd2634ad2ce
-- title:
--   Point Step Compare: pos Def of int
-- statement:
--   The Point Step Compare construction uses the pos Def of int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumPosOfTensorPos.lean#L116-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumPosOfTensorPos.lean#L116-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumPosOfTensorPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PointStepCompare
open NumberField Matrix
open scoped MatrixOrder

theorem GlobalTheory.PointStepCompare.posDef_of_int {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) (hs : ∀ i j, M i j = M j i)
    (hp : ∀ x : ι → ℤ, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x) :
    M.det ≠ 0 ∧ (M.map (Int.cast : ℤ → ℝ)).PosDef := by sorry
