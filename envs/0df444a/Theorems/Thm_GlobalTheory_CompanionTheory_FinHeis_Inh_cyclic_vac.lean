-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Inh_cyclic_vac
-- name    : GlobalTheory.CompanionTheory.FinHeis.Inh.cyclic_vac
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:45.404643+00:00
-- url     : https://prove2.me/theorems/8321489c-f3a6-4502-b152-bf3960ab188b
-- title:
--   Inh: cyclic vac
-- statement:
--   The Inh construction uses the cyclic vac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L391-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L391-L403

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
variable {S}
open GlobalTheory.CompanionTheory.FinHeis.Inh

theorem GlobalTheory.CompanionTheory.FinHeis.Inh.cyclic_vac : Cyclic sysEx vac := by sorry
