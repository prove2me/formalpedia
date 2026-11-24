-- Prove2me | Theorems.Thm_GlobalTheory_Descent_fg_of_baseChange
-- name    : GlobalTheory.Descent.fg_of_baseChange
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:43:40.935998+00:00
-- url     : https://prove2.me/theorems/620630f7-7e75-4c50-8e48-ce41f3cfe456
-- title:
--   Descent: fg of base Change
-- statement:
--   The Descent construction uses the fg of base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SpanSingletonEqTopIffIsUnitOfIsBaseChange.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SpanSingletonEqTopIffIsUnitOfIsBaseChange.lean#L20-L26

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

theorem GlobalTheory.Descent.fg_of_baseChange {N : Submodule A M} (h : (N.baseChange A').FG) : N.FG := by sorry
