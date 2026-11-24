-- Prove2me | Theorems.Thm_GlobalTheory_exists_invariant_notMem_orbit_generator
-- name    : GlobalTheory.exists_invariant_notMem_orbit_generator
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:26.048172+00:00
-- url     : https://prove2.me/theorems/e308852b-07b7-4330-af4f-ac42dffdb471
-- title:
--   Global Theory: exists invariant not Mem orbit generator
-- statement:
--   The Global Theory construction uses the exists invariant not Mem orbit generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L654-L670
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L654-L670

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
variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]

theorem GlobalTheory.exists_invariant_notMem_orbit_generator (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G A] (M : Type*) [AddCommGroup M] [Module A M] [Module.Invertible A M]
    (Q : Ideal A) [Q.IsPrime] :
    ∃ (s : A) (e : M), (∀ g : G, g • s = s) ∧ (∀ g : G, s ∉ g • Q) ∧
      ∃ f : Module.Dual A M, f e = s := by sorry
