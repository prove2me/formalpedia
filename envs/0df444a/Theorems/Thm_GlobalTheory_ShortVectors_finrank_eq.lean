-- Prove2me | Theorems.Thm_GlobalTheory_ShortVectors_finrank_eq
-- name    : GlobalTheory.ShortVectors.finrank_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:38.291334+00:00
-- url     : https://prove2.me/theorems/e47a33f2-97e9-4118-bd06-357a48f7886c
-- title:
--   Short Vectors: finrank eq
-- statement:
--   The Short Vectors construction uses the finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TraceHermNondegenerate.lean#L250-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TraceHermNondegenerate.lean#L250-L252

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

theorem GlobalTheory.ShortVectors.finrank_eq : finrank ℚ E = 2 * fdeg E := by sorry
