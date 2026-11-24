-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_ip_rho
-- name    : GlobalTheory.CompanionTheory.FinHeis.ip_rho
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:40:57.20584+00:00
-- url     : https://prove2.me/theorems/2b160181-3548-4bdd-aab7-12b23cad22fa
-- title:
--   Fin Heis: ip rho
-- statement:
--   The Fin Heis construction uses the ip rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L58-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L58-L58

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

theorem GlobalTheory.CompanionTheory.FinHeis.ip_rho (x : X) (u v : M) : ip S (S.rho x u) (S.rho x v) = ip S u v := by sorry
