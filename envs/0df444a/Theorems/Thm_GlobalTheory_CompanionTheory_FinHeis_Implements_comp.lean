-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_comp
-- name    : GlobalTheory.CompanionTheory.FinHeis.Implements.comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:22.361888+00:00
-- url     : https://prove2.me/theorems/018c645d-3c2e-4dcd-bff4-4f9daf54bd10
-- title:
--   Implements: comp
-- statement:
--   The Implements construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L190-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L190-L192

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

theorem GlobalTheory.CompanionTheory.FinHeis.Implements.comp {g g' : X ≃+ X} {T T' : M →ₗ[ℂ] M} (h : Implements S g T) (h' : Implements S g' T') :
    Implements S (g'.trans g) (T ∘ₗ T') := by sorry
