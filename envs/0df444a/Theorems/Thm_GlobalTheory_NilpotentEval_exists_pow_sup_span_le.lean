-- Prove2me | Theorems.Thm_GlobalTheory_NilpotentEval_exists_pow_sup_span_le
-- name    : GlobalTheory.NilpotentEval.exists_pow_sup_span_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:03.676345+00:00
-- url     : https://prove2.me/theorems/f76d2d67-233e-4ded-81d3-1e817baeb45f
-- title:
--   Nilpotent Eval: exists pow sup span le
-- statement:
--   The Nilpotent Eval construction uses the exists pow sup span le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesEvalOfPowMem.lean#L38-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesEvalOfPowMem.lean#L38-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesEvalOfPowMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
open GlobalTheory.NilpotentEval
variable {A : Type*} [CommRing A]

theorem GlobalTheory.NilpotentEval.exists_pow_sup_span_le (K : Ideal A) {σ : Type*} [Finite σ] (a : σ → A)
    (ha : ∀ j, ∃ M : ℕ, a j ^ M ∈ K) : ∃ N : ℕ, (K ⊔ Ideal.span (Set.range a)) ^ N ≤ K := by sorry
