-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_c_ne_zero
-- name    : GlobalTheory.CompanionTheory.FinHeis.Sys.c_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:39:46.683351+00:00
-- url     : https://prove2.me/theorems/07836c0c-f36f-4df1-a55b-bf9cf59e5ab8
-- title:
--   Sys: c ne zero
-- statement:
--   The Sys construction uses the c ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L74-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L74-L78

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

theorem GlobalTheory.CompanionTheory.FinHeis.Sys.c_ne_zero (x y : X) : S.c x y ≠ 0 := by sorry
