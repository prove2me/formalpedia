-- Prove2me | Theorems.Thm_GlobalTheory_WithAction_toBase_linearEquiv
-- name    : GlobalTheory.WithAction.toBase_linearEquiv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:34.371606+00:00
-- url     : https://prove2.me/theorems/30566ec0-7117-5089-a82c-059c178d65ab
-- title:
--   With Action: to Base linear Equiv
-- statement:
--   The With Action construction uses the to Base linear Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ToAbSheafPreservesFiniteLimits.lean#L194-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ToAbSheafPreservesFiniteLimits.lean#L194-L195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_SubsingletonOfSubsingletonFreeSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe w v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
open GlobalTheory.WithAction
variable {A M N : Type*} [CommRing A] [AddCommGroup M] [AddCommGroup N]
  (ρ : A →+* AddMonoid.End M) (σ : A →+* AddMonoid.End N)
variable (R : Type*) [CommRing R] [Algebra R A]

theorem GlobalTheory.WithAction.toBase_linearEquiv (f : M ≃+ N) (h : ∀ a x, f (ρ a x) = σ a (f x)) (x : WithAction ρ) :
    toBase σ (linearEquiv ρ σ R f h x) = f (toBase ρ x) := by sorry
