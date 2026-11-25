-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSumBound_finsum_le
-- name    : GlobalTheory.ThetaSumBound.finsum_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:01:27.489381+00:00
-- url     : https://prove2.me/theorems/71a6b5f0-5662-4d6d-819a-fb26ebe39fb5
-- title:
--   Theta Sum Bound: finsum le
-- statement:
--   The Theta Sum Bound construction uses the finsum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstMinimumSqMulIInfHeightLeCard.lean#L159-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstMinimumSqMulIInfHeightLeCard.lean#L159-L178

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsThetaRunParametersUniformTorusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstMinimumSqMulIInfHeightLeCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.ThetaSumBound
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [IsCMField E]

theorem GlobalTheory.ThetaSumBound.finsum_le (T : PT E) (S : Set (Fin T.r → Vsp T.dim))
    (hS : ∀ a ∈ S, (∀ j, a j ∈ ZSpan.fundamentalDomain T.b) ∧ ∀ j, ((5 : ℂ) ^ 2) • a j ∈ T.L)
    (f : (Fin T.r → Vsp T.dim) → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ a ∈ S, f a ≤ M) :
    ∑ᶠ (a) (_ : a ∈ S), f a ≤ (25 : ℝ) ^ (2 * (Module.finrank ℚ E * T.r) * T.r) * M := by sorry
