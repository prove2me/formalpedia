-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_c_zero_left
-- name    : GlobalTheory.CompanionTheory.FinHeis.Sys.c_zero_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:00:57.496528+00:00
-- url     : https://prove2.me/theorems/c129a13f-d523-4a32-89f3-24c97747096f
-- title:
--   Sys: c zero left
-- statement:
--   The Sys construction uses the c zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L85-L87

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinHeis
variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
open GlobalTheory.CompanionTheory.FinHeis.Sys

theorem GlobalTheory.CompanionTheory.FinHeis.Sys.c_zero_left (x : X) : S.c 0 x = 1 := by sorry
