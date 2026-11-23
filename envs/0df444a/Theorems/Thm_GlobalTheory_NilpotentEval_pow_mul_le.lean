-- Prove2me | Theorems.Thm_GlobalTheory_NilpotentEval_pow_mul_le
-- name    : GlobalTheory.NilpotentEval.pow_mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:24.682573+00:00
-- url     : https://prove2.me/theorems/06d26871-a010-4476-ba5b-4bc1f26c253a
-- title:
--   Nilpotent Eval: pow mul le
-- statement:
--   The Nilpotent Eval construction uses the pow mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesEvalOfPowMem.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesEvalOfPowMem.lean#L12-L14

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

theorem GlobalTheory.NilpotentEval.pow_mul_le {K J : Ideal A} {N : ℕ} (h : J ^ N ≤ K) (n : ℕ) : J ^ (N * n) ≤ K ^ n := by sorry
