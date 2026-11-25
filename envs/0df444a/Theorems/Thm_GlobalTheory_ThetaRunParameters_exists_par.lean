-- Prove2me | Theorems.Thm_GlobalTheory_ThetaRunParameters_exists_par
-- name    : GlobalTheory.ThetaRunParameters.exists_par
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:00:21.108512+00:00
-- url     : https://prove2.me/theorems/64b841dc-b33d-4a0c-b03b-c134daf3ba6e
-- title:
--   Theta Run Parameters: exists par
-- statement:
--   The Theta Run Parameters construction uses the exists par property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsThetaRunParametersUniformTorus.lean#L32-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsThetaRunParametersUniformTorus.lean#L32-L75

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

theorem GlobalTheory.ThetaRunParameters.exists_par : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r m : ℕ),
    2 ≤ PT.f E * r → 1 ≤ m → m ^ 4 ≤ PT.f E → (PT.f E : ℝ) ≤ PT.rd E →
    (PT.f E : ℝ) ^ 2 ≤ PT.rd E → 16 ≤ PT.rd E →
    ∃ (q : ℕ) (R0 : ℝ), 0 < th (E := E) q R0 ∧ ∀ X : PT E, X.r = r → (∃ τ, X.dim τ ≤ m) →
      ∃ P : Par X 1, P.q = q ∧ P.R0 = R0 ∧ P.m = m := by sorry
