-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Inh_alEx_nontrivial
-- name    : GlobalTheory.CompanionTheory.FinHeis.Inh.alEx_nontrivial
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:48.922957+00:00
-- url     : https://prove2.me/theorems/61084b98-5f6c-462c-82d1-c5737c51b695
-- title:
--   Inh: al Ex nontrivial
-- statement:
--   The Inh construction uses the al Ex nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L374-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L374-L375

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

theorem GlobalTheory.CompanionTheory.FinHeis.Inh.alEx_nontrivial : ((1, 2) : ZMod 4 × ZMod 4) ∈ G₁ ∧ alEx (1, 2) = -1 ∧ alEx (1, 0) = 1 ∧ alEx (0, 2) = 1 := by sorry
