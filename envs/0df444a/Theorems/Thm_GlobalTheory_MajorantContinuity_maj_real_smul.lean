-- Prove2me | Theorems.Thm_GlobalTheory_MajorantContinuity_maj_real_smul
-- name    : GlobalTheory.MajorantContinuity.maj_real_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:07:00.117467+00:00
-- url     : https://prove2.me/theorems/f9470452-bc0b-4eb7-aa93-788debb095e2
-- title:
--   Majorant Continuity: maj real smul
-- statement:
--   The Majorant Continuity construction uses the maj real smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/EventuallyComparable.lean#L36-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/EventuallyComparable.lean#L36-L45

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

theorem GlobalTheory.MajorantContinuity.maj_real_smul {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (t : ℝ) (v : Fin r → ℂ) :
    X.maj x τ ((t : ℂ) • v) = t ^ 2 * X.maj x τ v := by sorry
