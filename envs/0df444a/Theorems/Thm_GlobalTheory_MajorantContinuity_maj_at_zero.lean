-- Prove2me | Theorems.Thm_GlobalTheory_MajorantContinuity_maj_at_zero
-- name    : GlobalTheory.MajorantContinuity.maj_at_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:06:45.66281+00:00
-- url     : https://prove2.me/theorems/fc2d1eec-d0f2-4fb1-8b83-6b3b70ef1578
-- title:
--   Majorant Continuity: maj at zero
-- statement:
--   The Majorant Continuity construction uses the maj at zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/EventuallyComparable.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/EventuallyComparable.lean#L94-L95

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

theorem GlobalTheory.MajorantContinuity.maj_at_zero {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) : X.maj x τ 0 = 0 := by sorry
