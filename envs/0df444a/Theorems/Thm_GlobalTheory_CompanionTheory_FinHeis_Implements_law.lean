-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_law
-- name    : GlobalTheory.CompanionTheory.FinHeis.Implements.law
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:33.283259+00:00
-- url     : https://prove2.me/theorems/c377d76f-71cc-4674-a741-581557ccbaa6
-- title:
--   Implements: law
-- statement:
--   The Implements construction uses the law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L215-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MembershipCriteria/LaEqSqrtSmulLam.lean#L215-L219

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

theorem GlobalTheory.CompanionTheory.FinHeis.Implements.law {g : X ≃+ X} {T : M →ₗ[ℂ] M} (h : Implements S g T) {al : X → ℂ} {Γ : AddSubgroup X}
    (hal : ∀ γ ∈ Γ, al (g γ) = al γ) {φ : M} (hφ : Law S al Γ φ) : Law S al (Γ.map g.toAddMonoidHom) (T φ) := by sorry
