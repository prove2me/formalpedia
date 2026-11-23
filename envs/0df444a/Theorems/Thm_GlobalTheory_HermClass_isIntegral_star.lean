-- Prove2me | Theorems.Thm_GlobalTheory_HermClass_isIntegral_star
-- name    : GlobalTheory.HermClass.isIntegral_star
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:51.789797+00:00
-- url     : https://prove2.me/theorems/9ae10ee1-6840-4232-a05a-34ba47f87ead
-- title:
--   Herm Class: is Integral star
-- statement:
--   The Herm Class construction uses the is Integral star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsIntMulIsIntegralOfTrace.lean#L81-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsIntMulIsIntegralOfTrace.lean#L81-L82

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

theorem GlobalTheory.HermClass.isIntegral_star {a : E} (ha : IsIntegral ℤ a) : IsIntegral ℤ (star a) := by sorry
