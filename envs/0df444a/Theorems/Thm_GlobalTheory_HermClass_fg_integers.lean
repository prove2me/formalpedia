-- Prove2me | Theorems.Thm_GlobalTheory_HermClass_fg_integers
-- name    : GlobalTheory.HermClass.fg_integers
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:22.2455+00:00
-- url     : https://prove2.me/theorems/7a6846e8-acca-42a8-8440-02ac215b83b0
-- title:
--   Herm Class: fg integers
-- statement:
--   The Herm Class construction uses the fg integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsIntMulIsIntegralOfTrace.lean#L74-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsIntMulIsIntegralOfTrace.lean#L74-L75

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
variable (E : Type) [Field E] [NumberField E]

theorem GlobalTheory.HermClass.fg_integers : (Subalgebra.toSubmodule (integralClosure ℤ E)).FG := by sorry
