-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_rho_comm
-- name    : GlobalTheory.CompanionTheory.FinHeis.Sys.rho_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:16.528095+00:00
-- url     : https://prove2.me/theorems/8935988b-b408-4c80-b17a-ccf29a82c77a
-- title:
--   Sys: rho comm
-- statement:
--   The Sys construction uses the rho comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L103-L106

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

theorem GlobalTheory.CompanionTheory.FinHeis.Sys.rho_comm (x y : X) (v : M) : S.rho x (S.rho y v) = S.c x y ^ 2 • S.rho y (S.rho x v) := by sorry
