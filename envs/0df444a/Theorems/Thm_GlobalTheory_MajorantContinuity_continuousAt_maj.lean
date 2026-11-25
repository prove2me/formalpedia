-- Prove2me | Theorems.Thm_GlobalTheory_MajorantContinuity_continuousAt_maj
-- name    : GlobalTheory.MajorantContinuity.continuousAt_maj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:46.122896+00:00
-- url     : https://prove2.me/theorems/af78fb75-8627-463c-a08d-6a7767c073fe
-- title:
--   Majorant Continuity: continuous At maj
-- statement:
--   The Majorant Continuity construction uses the continuous At maj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/EventuallyComparable.lean#L47-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/EventuallyComparable.lean#L47-L84

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

theorem GlobalTheory.MajorantContinuity.continuousAt_maj {r : ℕ} (X : Data E r) (τ : X.Ψ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (v : Fin r → ℂ) :
    ContinuousAt (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2) (x, v) := by sorry
