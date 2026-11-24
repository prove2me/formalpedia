-- Prove2me | Theorems.Thm_GlobalTheory_ShortVectors_two_mul_le_traceHerm
-- name    : GlobalTheory.ShortVectors.two_mul_le_traceHerm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:11:56.119726+00:00
-- url     : https://prove2.me/theorems/ce78ebe2-1cba-4679-b0c6-b0d0c33e040f
-- title:
--   Short Vectors: two mul le trace Herm
-- statement:
--   The Short Vectors construction uses the two mul le trace Herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TraceHermNondegenerate.lean#L179-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TraceHermNondegenerate.lean#L179-L197

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open GlobalTheory
open GlobalTheory.ShortVectors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.ShortVectors.two_mul_le_traceHerm {n : ℕ} (x : Fin n → E) (τ : E →+* ℂ) :
    2 * ∑ k, ‖τ (x k)‖ ^ 2 ≤ (traceHerm n x x : ℝ) := by sorry
