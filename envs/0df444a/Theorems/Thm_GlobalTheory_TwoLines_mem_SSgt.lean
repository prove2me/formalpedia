-- Prove2me | Theorems.Thm_GlobalTheory_TwoLines_mem_SSgt
-- name    : GlobalTheory.TwoLines.mem_SSgt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:48.774693+00:00
-- url     : https://prove2.me/theorems/ce9f68f6-9fa4-5466-9fe9-ce143cff4d31
-- title:
--   Two Lines: mem SSgt
-- statement:
--   The Two Lines construction uses the mem SSgt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RightMulBorelFirstColumn.lean#L169-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RightMulBorelFirstColumn.lean#L169-L182

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfHermOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn
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

theorem GlobalTheory.TwoLines.mem_SSgt {X : Data E 2} (hG : X.Gm = 1) (hΓ : X.Γ = ⊥) {la : Wt X.Ψ 2}
    {m : ℕ} (h0 : ∀ τ, la τ 0 = m) (h1 : ∀ τ, la τ 1 = 0) {P : Frame X.Ψ 2 → ℂ}
    (hd : Differentiable ℂ P)
    (he : ∀ x, ∀ b ∈ Bor X.Ψ 2, P (rmul x b) = (∏ τ, b τ 0 0) ^ m * P x)
    {C : ℝ} (hb : ∀ x, ‖P x‖ ^ 2 ≤ C * (∏ τ, colSq x τ) ^ m) (c : ℝ) : P ∈ X.SSgt la c := by sorry
