-- Prove2me | Theorems.Thm_GlobalTheory_MajorantOrthFrame_sum_castLE_eq
-- name    : GlobalTheory.MajorantOrthFrame.sum_castLE_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:19:54.485886+00:00
-- url     : https://prove2.me/theorems/ba6beae7-adee-41db-8288-4213e03e19b3
-- title:
--   Majorant Orth Frame: sum cast LE eq
-- statement:
--   The Majorant Orth Frame construction uses the sum cast LE eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MajorantEqSumNormSqOrthonormalFrame.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MajorantEqSumNormSqOrthonormalFrame.lean#L13-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajorantEqSumNormSqOrthonormalFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.MajorantOrthFrame
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.MajorantOrthFrame.sum_castLE_eq {p r : ℕ} (h : p ≤ r) (f : Fin r → ℝ) :
    ∑ a : Fin p, f (Fin.castLE h a) = ∑ a : Fin r, if (a : ℕ) < p then f a else 0 := by sorry
