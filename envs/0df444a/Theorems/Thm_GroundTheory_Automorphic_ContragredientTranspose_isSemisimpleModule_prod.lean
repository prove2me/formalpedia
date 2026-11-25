-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_isSemisimpleModule_prod
-- name    : GroundTheory.Automorphic.ContragredientTranspose.isSemisimpleModule_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:57:23.591722+00:00
-- url     : https://prove2.me/theorems/1f89349f-59b1-4ded-98da-fa253f0b9c54
-- title:
--   Contragredient Transpose: is Semisimple Module prod
-- statement:
--   The Contragredient Transpose construction uses the is Semisimple Module prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L301-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/Character.lean#L301-L310

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MeasureTheory Module Whittaker
open HeckeAlgebra

theorem GroundTheory.Automorphic.ContragredientTranspose.isSemisimpleModule_prod {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [IsSemisimpleModule R M] [IsSemisimpleModule R N] :
    IsSemisimpleModule R (M × N) := by sorry
