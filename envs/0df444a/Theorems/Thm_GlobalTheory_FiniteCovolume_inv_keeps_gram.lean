-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCovolume_inv_keeps_gram
-- name    : GlobalTheory.FiniteCovolume.inv_keeps_gram
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:19.551858+00:00
-- url     : https://prove2.me/theorems/7ec7a6f3-0680-4d4e-aef9-9f7c77eb9865
-- title:
--   Finite Covolume: inv keeps gram
-- statement:
--   The Finite Covolume construction uses the inv keeps gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IsOrthUpdateMulInv.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IsOrthUpdateMulInv.lean#L13-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsOrthUpdateMulInv
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
open GlobalTheory GlobalTheory.FiniteCovolume
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.FiniteCovolume.inv_keeps_gram {r : ℕ} {J a : Matrix (Fin r) (Fin r) ℂ} (hJ : J.det ≠ 0)
    (ha : aᵀ * J * a.map (starRingEnd ℂ) = J) :
    (a⁻¹)ᵀ * J * (a⁻¹).map (starRingEnd ℂ) = J := by sorry
