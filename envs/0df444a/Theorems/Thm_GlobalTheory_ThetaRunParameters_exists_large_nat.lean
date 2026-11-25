-- Prove2me | Theorems.Thm_GlobalTheory_ThetaRunParameters_exists_large_nat
-- name    : GlobalTheory.ThetaRunParameters.exists_large_nat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:52:43.133949+00:00
-- url     : https://prove2.me/theorems/51996a40-92fa-40df-aae3-aa6f915198b8
-- title:
--   Theta Run Parameters: exists large nat
-- statement:
--   The Theta Run Parameters construction uses the exists large nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsThetaRunParametersUniformTorus.lean#L9-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsThetaRunParametersUniformTorus.lean#L9-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsThetaRunParametersUniformTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.ThetaRunParameters

theorem GlobalTheory.ThetaRunParameters.exists_large_nat (B c₁ c₂ d C : ℝ) (hB : 0 < B) (hd : 0 ≤ d) :
    ∃ q : ℕ, 1 ≤ q ∧ c₁ < q ∧ c₂ ≤ (q : ℝ) / 2 ∧ 1 ≤ (q : ℝ) / B ∧
      4 * (7 + Real.log q) + d + 1 ≤ q * ((q : ℝ) / B) ∧ C ≤ q * ((q : ℝ) / B) := by sorry
