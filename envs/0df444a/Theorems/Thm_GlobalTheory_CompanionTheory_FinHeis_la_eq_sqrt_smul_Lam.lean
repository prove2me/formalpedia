-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_la_eq_sqrt_smul_Lam
-- name    : GlobalTheory.CompanionTheory.FinHeis.la_eq_sqrt_smul_Lam
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:00:54.973799+00:00
-- url     : https://prove2.me/theorems/a40c187c-9977-4911-9d90-1706650f5c6a
-- title:
--   Fin Heis: la eq sqrt smul Lam
-- statement:
--   The Fin Heis construction uses the la eq sqrt smul Lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L161-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L161-L166

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

theorem GlobalTheory.CompanionTheory.FinHeis.la_eq_sqrt_smul_Lam (al : X → ℂ) {Γ Γ' : AddSubgroup X} (hN : Γ.relIndex Γ' ≠ 0) (φ : M) :
    la S al Γ' Γ φ = ((Real.sqrt (Γ.relIndex Γ' : ℝ) : ℝ) : ℂ) • abelian₂ S al Γ' Γ φ := by sorry
