-- Prove2me | Theorems.Thm_GlobalTheory_FlagFlowCheck_flowMat_eq_transv
-- name    : GlobalTheory.FlagFlowCheck.flowMat_eq_transv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:04.113701+00:00
-- url     : https://prove2.me/theorems/f790010c-c9ef-5426-b504-862dd06077f6
-- title:
--   Flag Flow Check: flow Mat eq transv
-- statement:
--   The Flag Flow Check construction uses the flow Mat eq transv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/FirstMinimumRankZero.lean#L45-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/FirstMinimumRankZero.lean#L45-L71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_FirstMinimumRankZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FlagFlowCheck
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem GlobalTheory.FlagFlowCheck.flowMat_eq_transv (ξ : Fin r → E) (τ : X.Ψ) (s : E) :
    X.flowMat ξ τ (τ.1 s) = (transvMat X.Gm ξ (s * X.κ0)).map τ.1 := by sorry
