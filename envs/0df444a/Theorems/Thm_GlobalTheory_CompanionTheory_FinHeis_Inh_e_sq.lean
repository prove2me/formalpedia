-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Inh_e_sq
-- name    : GlobalTheory.CompanionTheory.FinHeis.Inh.e_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:20.253525+00:00
-- url     : https://prove2.me/theorems/1e21aca1-c992-4a5f-bd57-a29e05d84b3e
-- title:
--   Inh: e sq
-- statement:
--   The Inh construction uses the e sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L256-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L256-L264

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

theorem GlobalTheory.CompanionTheory.FinHeis.Inh.e_sq (n : ZMod 4) : e n ^ 2 = 1 ↔ 2 * n = 0 := by sorry
