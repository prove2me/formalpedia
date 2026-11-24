-- Prove2me | Theorems.Thm_GlobalTheory_RowFubini_mem_conjSub
-- name    : GlobalTheory.RowFubini.mem_conjSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:09.893263+00:00
-- url     : https://prove2.me/theorems/1de96f7e-0663-44d5-817b-805835d2c4ba
-- title:
--   Row Fubini: mem conj Sub
-- statement:
--   The Row Fubini construction uses the mem conj Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L139-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L139-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise ENNReal
open GlobalTheory GlobalTheory.RowFubini
variable {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
omit [TopologicalSpace X] [IsTopologicalGroup X]

theorem GlobalTheory.RowFubini.mem_conjSub (K : Subgroup X) (b x : X) : x ∈ conjSub K b ↔ b⁻¹ * x * b ∈ K := by sorry
