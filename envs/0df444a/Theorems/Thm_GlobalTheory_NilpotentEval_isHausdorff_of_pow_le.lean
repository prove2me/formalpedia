-- Prove2me | Theorems.Thm_GlobalTheory_NilpotentEval_isHausdorff_of_pow_le
-- name    : GlobalTheory.NilpotentEval.isHausdorff_of_pow_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:34:01.950892+00:00
-- url     : https://prove2.me/theorems/767f24cc-ff03-4a6d-89ad-f07e3d7fc1e6
-- title:
--   Nilpotent Eval: is Hausdorff of pow le
-- statement:
--   The Nilpotent Eval construction uses the is Hausdorff of pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesEvalOfPowMem.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/MvPowerSeriesEvalOfPowMem.lean#L16-L22

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

theorem GlobalTheory.NilpotentEval.isHausdorff_of_pow_le {K J : Ideal A} {N : ℕ} (h : J ^ N ≤ K) [IsHausdorff K A] :
    IsHausdorff J A := by sorry
