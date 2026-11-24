-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_rho_bijective
-- name    : GlobalTheory.CompanionTheory.FinHeis.Sys.rho_bijective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:40:58.57602+00:00
-- url     : https://prove2.me/theorems/bab2accf-f0a1-444b-b8f7-1658acc49e5c
-- title:
--   Sys: rho bijective
-- statement:
--   The Sys construction uses the rho bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L100-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L100-L101

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

theorem GlobalTheory.CompanionTheory.FinHeis.Sys.rho_bijective (x : X) : Function.Bijective (S.rho x) := by sorry
