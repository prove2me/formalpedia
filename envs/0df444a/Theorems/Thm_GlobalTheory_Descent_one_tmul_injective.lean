-- Prove2me | Theorems.Thm_GlobalTheory_Descent_one_tmul_injective
-- name    : GlobalTheory.Descent.one_tmul_injective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:05.068858+00:00
-- url     : https://prove2.me/theorems/31f93bb7-3be0-5446-ba1f-c79347cb7275
-- title:
--   Descent: one tmul injective
-- statement:
--   The Descent construction uses the one tmul injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SpanSingletonEqTopIffIsUnitOfIsBaseChange.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SpanSingletonEqTopIffIsUnitOfIsBaseChange.lean#L56-L57

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

theorem GlobalTheory.Descent.one_tmul_injective : Function.Injective fun m : M ↦ (1 : A') ⊗ₜ[A] m := by sorry
