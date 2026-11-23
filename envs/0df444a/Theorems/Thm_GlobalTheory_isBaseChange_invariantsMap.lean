-- Prove2me | Theorems.Thm_GlobalTheory_isBaseChange_invariantsMap
-- name    : GlobalTheory.isBaseChange_invariantsMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:09.125888+00:00
-- url     : https://prove2.me/theorems/496cf4ee-858d-429d-8f6c-97ebf1f11f94
-- title:
--   Global Theory: is Base Change invariants Map
-- statement:
--   The Global Theory construction uses the is Base Change invariants Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L174-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L174-L181

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Module S M']
  [IsScalarTower R S M']
variable {G : Type*} [Group G]

theorem GlobalTheory.isBaseChange_invariantsMap [Finite G] [Module.Flat R S] (ρ : Representation R G M)
    (ρ' : Representation S G M') (f : M →ₗ[R] M') (hb : IsBaseChange S f)
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) : IsBaseChange S (invariantsMap ρ ρ' f hf) := by sorry
