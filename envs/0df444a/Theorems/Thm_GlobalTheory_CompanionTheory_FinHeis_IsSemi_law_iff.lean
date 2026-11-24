-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_IsSemi_law_iff
-- name    : GlobalTheory.CompanionTheory.FinHeis.IsSemi.law_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:39:27.964798+00:00
-- url     : https://prove2.me/theorems/afa96137-1f5c-482a-8024-ecc29879639c
-- title:
--   Is Semi: law iff
-- statement:
--   The Is Semi construction uses the law iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L129-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L129-L135

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

theorem GlobalTheory.CompanionTheory.FinHeis.IsSemi.law_iff {al : X → ℂ} {Γ : AddSubgroup X} (h : IsSemi S al Γ) (φ : M) :
    Law S al Γ φ ↔ ∀ γ ∈ Γ, al γ • S.rho γ φ = φ := by sorry
