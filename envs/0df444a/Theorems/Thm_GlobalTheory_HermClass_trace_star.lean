-- Prove2me | Theorems.Thm_GlobalTheory_HermClass_trace_star
-- name    : GlobalTheory.HermClass.trace_star
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:12.304921+00:00
-- url     : https://prove2.me/theorems/69f76eda-5bf6-4299-8e53-882325852c52
-- title:
--   Herm Class: trace star
-- statement:
--   The Herm Class construction uses the trace star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsIntMulIsIntegralOfTrace.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsIntMulIsIntegralOfTrace.lean#L84-L85

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsShortOfTraceDet_f72bcdc76e7ca34f
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open Module Submodule NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.HermClass.trace_star (a : E) : Algebra.trace ℚ E (star a) = Algebra.trace ℚ E a := by sorry
