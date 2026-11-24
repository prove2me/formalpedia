-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_c_zero_right
-- name    : GlobalTheory.CompanionTheory.FinHeis.Sys.c_zero_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:21.439015+00:00
-- url     : https://prove2.me/theorems/564ae94a-eb1a-40ff-b0d2-27a56816cde6
-- title:
--   Sys: c zero right
-- statement:
--   The Sys construction uses the c zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L80-L83

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

theorem GlobalTheory.CompanionTheory.FinHeis.Sys.c_zero_right (x : X) : S.c x 0 = 1 := by sorry
