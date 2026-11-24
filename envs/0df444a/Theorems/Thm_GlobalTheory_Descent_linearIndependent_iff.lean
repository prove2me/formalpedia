-- Prove2me | Theorems.Thm_GlobalTheory_Descent_linearIndependent_iff
-- name    : GlobalTheory.Descent.linearIndependent_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:42:20.177446+00:00
-- url     : https://prove2.me/theorems/aa27e03c-7637-46c8-b396-fd65d0e99366
-- title:
--   Descent: linear Independent iff
-- statement:
--   The Descent construction uses the linear Independent iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SpanSingletonEqTopIffIsUnitOfIsBaseChange.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SpanSingletonEqTopIffIsUnitOfIsBaseChange.lean#L59-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
open GlobalTheory.Descent
variable {A : Type*} (A' : Type*) [CommRing A] [CommRing A'] [Algebra A A']
  [Module.FaithfullyFlat A A'] {M : Type*} [AddCommGroup M] [Module A M]

theorem GlobalTheory.Descent.linearIndependent_iff {ι : Type*} (v : ι → M) :
    LinearIndependent A v ↔ LinearIndependent A' fun i ↦ (1 : A') ⊗ₜ[A] v i := by sorry
