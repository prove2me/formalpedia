-- Prove2me | Theorems.Thm_GlobalTheory_ShortVectors_traceHerm_apply
-- name    : GlobalTheory.ShortVectors.traceHerm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:07:21.739853+00:00
-- url     : https://prove2.me/theorems/fbb5c222-8a39-4bfb-ab0b-8855104d8562
-- title:
--   Short Vectors: trace Herm apply
-- statement:
--   The Short Vectors construction uses the trace Herm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TraceHermNondegenerate.lean#L155-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TraceHermNondegenerate.lean#L155-L156

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

theorem GlobalTheory.ShortVectors.traceHerm_apply {n : ℕ} (x y : Fin n → E) :
    traceHerm n x y = Algebra.trace ℚ E (herm 1 x y) := by sorry
