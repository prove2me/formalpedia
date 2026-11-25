-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_ip_rho_eq_zero
-- name    : GlobalTheory.CompanionTheory.FinHeis.ip_rho_eq_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:00:42.847797+00:00
-- url     : https://prove2.me/theorems/a65449c4-7a44-5a8f-8289-e32e69252332
-- title:
--   Fin Heis: ip rho eq zero
-- statement:
--   The Fin Heis construction uses the ip rho eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L176-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L176-L186

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

theorem GlobalTheory.CompanionTheory.FinHeis.ip_rho_eq_zero {al : X → ℂ} {Γ : AddSubgroup X} (hΓ : SelfDual S Γ) (h : IsSemi S al Γ) {φ : M}
    (hφ : Law S al Γ φ) {x : X} (hx : x ∉ Γ) : ip S (S.rho x φ) φ = 0 := by sorry
