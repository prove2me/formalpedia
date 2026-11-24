-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_c_neg_self
-- name    : GlobalTheory.CompanionTheory.FinHeis.Sys.c_neg_self
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:39:47.539776+00:00
-- url     : https://prove2.me/theorems/df9f6e8d-d6c8-48f4-bda2-25578ca314a2
-- title:
--   Sys: c neg self
-- statement:
--   The Sys construction uses the c neg self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L89-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L89-L92

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

theorem GlobalTheory.CompanionTheory.FinHeis.Sys.c_neg_self (x : X) : S.c x (-x) = 1 := by sorry
