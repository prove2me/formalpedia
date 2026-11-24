-- Prove2me | Theorems.Thm_GlobalTheory_MajorantContinuity_hermC_smul_l
-- name    : GlobalTheory.MajorantContinuity.hermC_smul_l
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:20:34.962205+00:00
-- url     : https://prove2.me/theorems/3eb53551-c2d6-4c9f-9bba-a4733dcb91e2
-- title:
--   Majorant Continuity: herm C smul l
-- statement:
--   The Majorant Continuity construction uses the herm C smul l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/EventuallyComparable.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/EventuallyComparable.lean#L14-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EventuallyComparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate ComplexOrder
open GlobalTheory GlobalTheory.MajorantContinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.MajorantContinuity.hermC_smul_l {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ) (u v : Fin r → ℂ) :
    hermC τ G (a • u) v = a * hermC τ G u v := by sorry
