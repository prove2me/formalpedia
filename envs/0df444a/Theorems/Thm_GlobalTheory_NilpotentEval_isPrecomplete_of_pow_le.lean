-- Prove2me | Theorems.Thm_GlobalTheory_NilpotentEval_isPrecomplete_of_pow_le
-- name    : GlobalTheory.NilpotentEval.isPrecomplete_of_pow_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:33:36.360268+00:00
-- url     : https://prove2.me/theorems/f057e113-d3ae-429b-a763-fe4038522f87
-- title:
--   Nilpotent Eval: is Precomplete of pow le
-- statement:
--   The Nilpotent Eval construction uses the is Precomplete of pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesEvalOfPowMem.lean#L24-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesEvalOfPowMem.lean#L24-L36

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

theorem GlobalTheory.NilpotentEval.isPrecomplete_of_pow_le {K J : Ideal A} {N : ℕ} (h : J ^ N ≤ K) (hKJ : K ≤ J)
    [IsPrecomplete K A] : IsPrecomplete J A := by sorry
