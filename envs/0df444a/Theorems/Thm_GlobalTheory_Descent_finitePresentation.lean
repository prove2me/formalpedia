-- Prove2me | Theorems.Thm_GlobalTheory_Descent_finitePresentation
-- name    : GlobalTheory.Descent.finitePresentation
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:43:10.541461+00:00
-- url     : https://prove2.me/theorems/ddd49f75-562e-4551-a9ed-274ec0dd9932
-- title:
--   Descent: finite Presentation
-- statement:
--   The Descent construction uses the finite Presentation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SpanSingletonEqTopIffIsUnitOfIsBaseChange.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SpanSingletonEqTopIffIsUnitOfIsBaseChange.lean#L28-L39

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

theorem GlobalTheory.Descent.finitePresentation [Module.FinitePresentation A' (A' ⊗[A] M)] :
    Module.FinitePresentation A M := by sorry
