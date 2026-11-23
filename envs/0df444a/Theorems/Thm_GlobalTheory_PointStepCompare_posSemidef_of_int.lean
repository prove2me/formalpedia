-- Prove2me | Theorems.Thm_GlobalTheory_PointStepCompare_posSemidef_of_int
-- name    : GlobalTheory.PointStepCompare.posSemidef_of_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:23.339439+00:00
-- url     : https://prove2.me/theorems/a3425712-2281-45fd-a831-53e4b4a76e8e
-- title:
--   Point Step Compare: pos Semidef of int
-- statement:
--   The Point Step Compare construction uses the pos Semidef of int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumPosOfTensorPos.lean#L95-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumPosOfTensorPos.lean#L95-L114

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

theorem GlobalTheory.PointStepCompare.posSemidef_of_int {ι : Type} [Fintype ι] {N : Matrix ι ι ℝ} (hH : N.IsHermitian)
    (hp : ∀ x : ι → ℤ, 0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ))) : N.PosSemidef := by sorry
