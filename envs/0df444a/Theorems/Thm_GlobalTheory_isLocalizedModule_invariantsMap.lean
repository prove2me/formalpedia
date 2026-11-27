-- Prove2me | Theorems.Thm_GlobalTheory_isLocalizedModule_invariantsMap
-- name    : GlobalTheory.isLocalizedModule_invariantsMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:33.666397+00:00
-- url     : https://prove2.me/theorems/47ccfd2e-87da-4b2a-b013-acd10fb18931
-- title:
--   Global Theory: is Localized Module invariants Map
-- statement:
--   The Global Theory construction uses the is Localized Module invariants Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L214-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L214-L220

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

theorem GlobalTheory.isLocalizedModule_invariantsMap [Finite G] (T : Submonoid R) [IsLocalization T S]
    (ρ : Representation R G M) (ρ' : Representation S G M') (f : M →ₗ[R] M')
    [IsLocalizedModule T f] (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) :
    IsLocalizedModule T (invariantsMap ρ ρ' f hf) := by sorry
