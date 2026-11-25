-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_unitVac_iff_ip
-- name    : GlobalTheory.CompanionTheory.FinHeis.unitVac_iff_ip
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:15.405803+00:00
-- url     : https://prove2.me/theorems/5c2ca2cb-4692-490a-b79e-6fa98fa9646c
-- title:
--   Fin Heis: unit Vac iff ip
-- statement:
--   The Fin Heis construction uses the unit Vac iff ip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L60-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L60-L61

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

theorem GlobalTheory.CompanionTheory.FinHeis.unitVac_iff_ip (al : X → ℂ) (Γ : AddSubgroup X) (φ : M) :
    UnitVac S al Γ φ ↔ Law S al Γ φ ∧ ip S φ φ = 1 := by sorry
