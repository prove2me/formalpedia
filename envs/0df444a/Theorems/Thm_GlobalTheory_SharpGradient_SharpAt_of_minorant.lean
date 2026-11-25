-- Prove2me | Theorems.Thm_GlobalTheory_SharpGradient_SharpAt_of_minorant
-- name    : GlobalTheory.SharpGradient.SharpAt.of_minorant
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:12:35.878882+00:00
-- url     : https://prove2.me/theorems/4e007f11-4acb-541f-8b53-26874de23823
-- title:
--   Sharp At: of minorant
-- statement:
--   The Sharp At construction uses the of minorant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ContinuousInvLeadingBlockEntry.lean#L24-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ContinuousInvLeadingBlockEntry.lean#L24-L56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
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
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
variable {n : ℕ}

theorem GlobalTheory.SharpGradient.SharpAt.of_minorant {φ ψ : V n → ℝ} {x : V n} {ξ : Fin n → ℂ} (h : SharpAt ψ x ξ)
    (hφ : ContDiffAt ℝ 2 φ x) (hle : ∀ᶠ v in 𝓝 x, ψ v ≤ φ v) (heq : φ x = ψ x) :
    SharpAt φ x ξ := by sorry
