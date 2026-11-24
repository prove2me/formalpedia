-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_IsSemi_conj_eq
-- name    : GlobalTheory.CompanionTheory.FinHeis.IsSemi.conj_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:39:40.92549+00:00
-- url     : https://prove2.me/theorems/2b5b1be1-16a2-45d1-9e81-aac1e7f9115b
-- title:
--   Is Semi: conj eq
-- statement:
--   The Is Semi construction uses the conj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L120-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L120-L122

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

theorem GlobalTheory.CompanionTheory.FinHeis.IsSemi.conj_eq {al : X → ℂ} {Γ : AddSubgroup X} (h : IsSemi S al Γ) {x : X} (hx : x ∈ Γ) :
    (starRingEnd ℂ) (al x) = al x := by sorry
