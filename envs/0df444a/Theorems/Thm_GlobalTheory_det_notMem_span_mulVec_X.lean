-- Prove2me | Theorems.Thm_GlobalTheory_det_notMem_span_mulVec_X
-- name    : GlobalTheory.det_notMem_span_mulVec_X
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:32.705188+00:00
-- url     : https://prove2.me/theorems/2f28dde3-c1a6-41a5-be87-26f32de04715
-- title:
--   Global Theory: det not Mem span mul Vec X
-- statement:
--   The Global Theory construction uses the det not Mem span mul Vec X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetNotMemSpanMulVecOfSocle.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetNotMemSpanMulVecOfSocle.lean#L51-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetUpdateRowAlternatingMulVecMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPowerSeriesVariablesSyzygySocle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetNotMemSpanMulVecOfSocle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.det_notMem_span_mulVec_X : ∀ (k : Type) [Field k] (g N : ℕ) (a : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k)), (∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin g) k) ^ N ∈ Ideal.span (Set.range (a.mulVec MvPowerSeries.X))) → a.det ∉ Ideal.span (Set.range (a.mulVec MvPowerSeries.X)) := by sorry
