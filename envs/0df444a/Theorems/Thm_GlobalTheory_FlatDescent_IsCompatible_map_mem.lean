-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_IsCompatible_map_mem
-- name    : GlobalTheory.FlatDescent.IsCompatible.map_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:32:08.355279+00:00
-- url     : https://prove2.me/theorems/a92c15d9-e840-40a3-8cbc-d0c1db501997
-- title:
--   Is Compatible: map mem
-- statement:
--   The Is Compatible construction uses the map mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean#L150-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean#L150-L154

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

theorem GlobalTheory.FlatDescent.IsCompatible.map_mem {θ : N →ₗ[B] B ⊗[A] N} {θ' : N' →ₗ[B] B ⊗[A] N'} {f : N →ₗ[B] N'}
    (hf : IsCompatible θ θ' f) {n : N} (hn : n ∈ invariants θ) : f n ∈ invariants θ' := by sorry
