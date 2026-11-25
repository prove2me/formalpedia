-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_ip_pos
-- name    : GlobalTheory.CompanionTheory.FinHeis.ip_pos
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:07.177903+00:00
-- url     : https://prove2.me/theorems/0e2ef322-1921-4f31-9328-2fdab568d943
-- title:
--   Fin Heis: ip pos
-- statement:
--   The Fin Heis construction uses the ip pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L56-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L56-L56

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

theorem GlobalTheory.CompanionTheory.FinHeis.ip_pos (v : M) (hv : v ≠ 0) : 0 < (ip S v v).re := by sorry
