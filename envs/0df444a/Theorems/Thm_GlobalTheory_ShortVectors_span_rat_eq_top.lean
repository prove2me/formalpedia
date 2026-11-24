-- Prove2me | Theorems.Thm_GlobalTheory_ShortVectors_span_rat_eq_top
-- name    : GlobalTheory.ShortVectors.span_rat_eq_top
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:11:57.246932+00:00
-- url     : https://prove2.me/theorems/4a7b2e64-762b-424f-bf96-c09ebf8f727b
-- title:
--   Short Vectors: span rat eq top
-- statement:
--   The Short Vectors construction uses the span rat eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TraceHermNondegenerate.lean#L215-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TraceHermNondegenerate.lean#L215-L248

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
omit [IsCMField E]

theorem GlobalTheory.ShortVectors.span_rat_eq_top {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (h : span E (Λ : Set (Fin n → E)) = ⊤) : span ℚ (Λ : Set (Fin n → E)) = ⊤ := by sorry
