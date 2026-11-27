-- Prove2me | Theorems.Thm_GlobalTheory_TwoLines_exists_two
-- name    : GlobalTheory.TwoLines.exists_two
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:11.027179+00:00
-- url     : https://prove2.me/theorems/4672d3a9-13f9-5514-a417-eec282f5ea7a
-- title:
--   Two Lines: exists two
-- statement:
--   The Two Lines construction uses the exists two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/EqZeroOfHermOne.lean#L181-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/EqZeroOfHermOne.lean#L181-L195

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfHermOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix
open GlobalTheory GlobalTheory.TwoLines
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.TwoLines.exists_two {r : ℕ} (X : Data E r) (h : Module.finrank ℚ E = 4) :
    ∃ τ₁ τ₂ : X.Ψ, τ₁ ≠ τ₂ ∧ ∀ τ, τ = τ₁ ∨ τ = τ₂ := by sorry
