-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_implements_iff_ip
-- name    : GlobalTheory.CompanionTheory.FinHeis.implements_iff_ip
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:00:32.520455+00:00
-- url     : https://prove2.me/theorems/a39b28bd-49f8-5ee5-95ca-2b0891e9ebb8
-- title:
--   Fin Heis: implements iff ip
-- statement:
--   The Fin Heis construction uses the implements iff ip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L63-L65

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

theorem GlobalTheory.CompanionTheory.FinHeis.implements_iff_ip (g : X ≃+ X) (T : M →ₗ[ℂ] M) :
    Implements S g T ↔ (∀ x v, T (S.rho x v) = S.rho (g x) (T v)) ∧ ∀ u v, ip S (T u) (T v) = ip S u v := by sorry
