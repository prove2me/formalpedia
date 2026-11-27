-- Prove2me | Theorems.Thm_GlobalTheory_span_inf_restrictScalars_of_isLocalization
-- name    : GlobalTheory.span_inf_restrictScalars_of_isLocalization
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:50.449219+00:00
-- url     : https://prove2.me/theorems/9725ec6c-be6e-5833-8196-bdd451448949
-- title:
--   Global Theory: span inf restrict Scalars of is Localization
-- statement:
--   The Global Theory construction uses the span inf restrict Scalars of is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L222-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L222-L258

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

theorem GlobalTheory.span_inf_restrictScalars_of_isLocalization (T : Submonoid R) [IsLocalization T S]
    (L : Submodule R M') (W : Submodule S M') :
    Submodule.span S ((L ⊓ W.restrictScalars R : Submodule R M') : Set M')
      = Submodule.span S (L : Set M') ⊓ W := by sorry
