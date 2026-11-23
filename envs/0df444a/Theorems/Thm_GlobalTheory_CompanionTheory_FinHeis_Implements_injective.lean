-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_injective
-- name    : GlobalTheory.CompanionTheory.FinHeis.Implements.injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:02.467464+00:00
-- url     : https://prove2.me/theorems/b6f5b61b-829a-45f6-acf7-eca684d0590d
-- title:
--   Implements: injective
-- statement:
--   The Implements construction uses the injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L194-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L194-L200

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

theorem GlobalTheory.CompanionTheory.FinHeis.Implements.injective {g : X ≃+ X} {T : M →ₗ[ℂ] M} (h : Implements S g T) : Function.Injective T := by sorry
