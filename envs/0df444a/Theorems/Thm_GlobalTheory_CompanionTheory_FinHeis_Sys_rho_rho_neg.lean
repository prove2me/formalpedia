-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_rho_rho_neg
-- name    : GlobalTheory.CompanionTheory.FinHeis.Sys.rho_rho_neg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:53.523969+00:00
-- url     : https://prove2.me/theorems/222934e6-4f11-4b60-8dcc-dd373b436b6d
-- title:
--   Sys: rho rho neg
-- statement:
--   The Sys construction uses the rho rho neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L94-L95

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

theorem GlobalTheory.CompanionTheory.FinHeis.Sys.rho_rho_neg (x : X) (v : M) : S.rho x (S.rho (-x) v) = v := by sorry
