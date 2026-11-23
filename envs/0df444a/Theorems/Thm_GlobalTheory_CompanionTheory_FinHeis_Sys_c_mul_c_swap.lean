-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_c_mul_c_swap
-- name    : GlobalTheory.CompanionTheory.FinHeis.Sys.c_mul_c_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:16.301994+00:00
-- url     : https://prove2.me/theorems/b6912671-1e16-4fae-9ee7-ae3b4b2bd101
-- title:
--   Sys: c mul c swap
-- statement:
--   The Sys construction uses the c mul c swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L69-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L69-L72

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

theorem GlobalTheory.CompanionTheory.FinHeis.Sys.c_mul_c_swap (x y : X) : S.c x y * S.c y x = 1 := by sorry
