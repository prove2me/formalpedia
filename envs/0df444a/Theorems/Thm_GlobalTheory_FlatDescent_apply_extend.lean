-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_apply_extend
-- name    : GlobalTheory.FlatDescent.apply_extend
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:32:08.074879+00:00
-- url     : https://prove2.me/theorems/9d9325b3-9ff5-494c-a75c-a97a7c3a3e70
-- title:
--   Flat Descent: apply extend
-- statement:
--   The Flat Descent construction uses the apply extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean#L71-L76

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

theorem GlobalTheory.FlatDescent.apply_extend (θ : N →ₗ[B] B ⊗[A] N) (x : B ⊗[A] invariants θ) :
    θ (extend B _ x) = (invariants θ).subtype.lTensor B x := by sorry
