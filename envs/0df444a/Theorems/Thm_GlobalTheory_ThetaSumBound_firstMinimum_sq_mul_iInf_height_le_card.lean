-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSumBound_firstMinimum_sq_mul_iInf_height_le_card
-- name    : GlobalTheory.ThetaSumBound.firstMinimum_sq_mul_iInf_height_le_card
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:00.833278+00:00
-- url     : https://prove2.me/theorems/1cb3691b-779e-4266-8f60-7844f604d670
-- title:
--   Theta Sum Bound: first Minimum sq mul i Inf height le card
-- statement:
--   The Theta Sum Bound construction uses the first Minimum sq mul i Inf height le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstMinimumSqMulIInfHeightLeCard.lean#L117-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstMinimumSqMulIInfHeightLeCard.lean#L117-L145

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

theorem GlobalTheory.ThetaSumBound.firstMinimum_sq_mul_iInf_height_le_card (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E}
    (hξ : ξ ∈ X.Λ) (h0 : ξ ≠ 0) : X.la1 x ^ 2 * ⨅ τ, X.tt ξ x τ ≤ Fintype.card X.Ψ := by sorry
