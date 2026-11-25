-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSumBound_log_le_of_bounds
-- name    : GlobalTheory.ThetaSumBound.log_le_of_bounds
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:10:45.658116+00:00
-- url     : https://prove2.me/theorems/78dcaf9f-33b5-5d5d-896f-3473b06e699b
-- title:
--   Theta Sum Bound: log le of bounds
-- statement:
--   The Theta Sum Bound construction uses the log le of bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstMinimumSqMulIInfHeightLeCard.lean#L57-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstMinimumSqMulIInfHeightLeCard.lean#L57-L101

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsThetaRunParametersUniformTorusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstMinimumSqMulIInfHeightLeCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.ThetaSumBound

theorem GlobalTheory.ThetaSumBound.log_le_of_bounds {K S la th c k B p3 p1 f t : ℝ} (hK : 0 < K) (hS : 0 < S) (hla : 0 < la)
    (hth : 0 < th) (hc : 0 < c) (hk : 0 < k) (hB : 0 ≤ B) (hf : 0 < f) (ht : la ^ 2 * t ≤ f)
    (h1 : la < th → S ≤ K * (Real.exp p3 * (k * (c / la ^ 2)) ^ B *
      Real.exp (-(Real.pi * (c / la ^ 2) / 5 ^ 4))) ^ 2)
    (h2 : th ≤ la → S ≤ K * Real.exp p1 ^ 2) :
    Real.log S ≤ (Real.log K + 2 * |p3| + 2 * B * |Real.log (k * c)| + 2 * |p1| +
      2 * Real.pi * c / (5 ^ 4 * th ^ 2)) + 4 * B * Real.log (1 + 1 / la) -
      2 * Real.pi * c / (5 ^ 4 * f) * t := by sorry
