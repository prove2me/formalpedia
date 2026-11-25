-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_c_map
-- name    : GlobalTheory.CompanionTheory.FinHeis.Implements.c_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:47.884601+00:00
-- url     : https://prove2.me/theorems/9ad6bce3-5497-4f4c-9bc3-eac74fb55fd5
-- title:
--   Implements: c map
-- statement:
--   The Implements construction uses the c map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L202-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L202-L213

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

theorem GlobalTheory.CompanionTheory.FinHeis.Implements.c_map [Nontrivial M] {g : X ≃+ X} {T : M →ₗ[ℂ] M} (h : Implements S g T) (x y : X) :
    S.c (g x) (g y) = S.c x y := by sorry
