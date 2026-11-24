-- Prove2me | Theorems.Thm_GlobalTheory_Descent_projective_of_isBaseChange
-- name    : GlobalTheory.Descent.projective_of_isBaseChange
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:43:04.129786+00:00
-- url     : https://prove2.me/theorems/ad6bcccf-51af-464b-a867-f7342c3d825c
-- title:
--   Descent: projective of is Base Change
-- statement:
--   The Descent construction uses the projective of is Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SpanSingletonEqTopIffIsUnitOfIsBaseChange.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SpanSingletonEqTopIffIsUnitOfIsBaseChange.lean#L85-L89

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
variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] [Module.FaithfullyFlat A A']
  {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] [Module A' M']
  [IsScalarTower A A' M'] {f : M →ₗ[A] M'} (hf : IsBaseChange A' f)
include hf

theorem GlobalTheory.Descent.projective_of_isBaseChange [Module.Finite A' M'] [Module.Projective A' M'] :
    Module.Projective A M := by sorry
