-- Prove2me | Theorems.Thm_GlobalTheory_ProperDiscontinuity_mat_oneFrame
-- name    : GlobalTheory.ProperDiscontinuity.mat_oneFrame
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:06:28.184263+00:00
-- url     : https://prove2.me/theorems/36ab8eaa-979c-4ed4-b395-53d9baadbe51
-- title:
--   Proper Discontinuity: mat one Frame
-- statement:
--   The Proper Discontinuity construction uses the mat one Frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RmulOneFrame.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RmulOneFrame.lean#L16-L16

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RmulOneFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.ProperDiscontinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.ProperDiscontinuity.mat_oneFrame (Ψ : Finset (E →+* ℂ)) (r : ℕ) (τ : Ψ) : mat (oneFrame Ψ r) τ = 1 := by sorry
