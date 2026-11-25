-- Prove2me | Theorems.Thm_GlobalTheory_LeadBound_IsDom_mul_pow
-- name    : GlobalTheory.LeadBound.IsDom.mul_pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:25:01.420498+00:00
-- url     : https://prove2.me/theorems/065eebda-3230-446d-9ecb-9cf748b0ec83
-- title:
--   Is Dom: mul pow
-- statement:
--   The Is Dom construction uses the mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MulProd.lean#L70-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MulProd.lean#L70-L76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MulProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LeadBound
open ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} (X : Data E r) (g : Frame X.Ψ r → ℝ)
variable {X g}

theorem GlobalTheory.LeadBound.IsDom.mul_pow {la L : Wt X.Ψ r} {n : ℕ} {P Q : Frame X.Ψ r → ℂ} (hQ : IsDom X g la n Q)
    (hP : IsDom X g L 1 P) (m : ℕ) : IsDom X g (la + m • L) (n + m) (Q * P ^ m) := by sorry
