-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_apply_extend_eq_canonical
-- name    : GlobalTheory.FlatDescent.apply_extend_eq_canonical
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:25.764638+00:00
-- url     : https://prove2.me/theorems/2120a3b8-23dc-4665-81ca-674a83c27e86
-- title:
--   Flat Descent: apply extend eq canonical
-- statement:
--   The Flat Descent construction uses the apply extend eq canonical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean#L78-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean#L78-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
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
open GlobalTheory.FlatDescent
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  {N' : Type*} [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']

theorem GlobalTheory.FlatDescent.apply_extend_eq_canonical (θ : N →ₗ[B] B ⊗[A] N) (x : B ⊗[A] invariants θ) :
    θ (extend B _ x) =
      ((extend B (invariants θ)).restrictScalars A).lTensor B (canonical B _ x) := by sorry
