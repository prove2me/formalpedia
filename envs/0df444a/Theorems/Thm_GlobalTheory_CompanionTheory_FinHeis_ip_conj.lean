-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_ip_conj
-- name    : GlobalTheory.CompanionTheory.FinHeis.ip_conj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:00:38.136123+00:00
-- url     : https://prove2.me/theorems/5363d9b2-5244-5dfd-ae00-47b83a91465b
-- title:
--   Fin Heis: ip conj
-- statement:
--   The Fin Heis construction uses the ip conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L54-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L54-L54

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

theorem GlobalTheory.CompanionTheory.FinHeis.ip_conj (u v : M) : (starRingEnd ℂ) (ip S u v) = ip S v u := by sorry
