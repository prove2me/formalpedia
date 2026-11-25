-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_IsCompatible_existsUnique_baseChange_eq
-- name    : GlobalTheory.FlatDescent.IsCompatible.existsUnique_baseChange_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:42.061689+00:00
-- url     : https://prove2.me/theorems/28e621ed-ccdf-53b9-9278-d09cc943d62b
-- title:
--   Is Compatible: exists Unique base Change eq
-- statement:
--   The Is Compatible construction uses the exists Unique base Change eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean#L183-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean#L183-L186

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
variable {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']

theorem GlobalTheory.FlatDescent.IsCompatible.existsUnique_baseChange_eq [Module.FaithfullyFlat A B]
    {f : B ⊗[A] M →ₗ[B] B ⊗[A] M'} (hf : IsCompatible (canonical B M) (canonical B M') f) :
    ∃! g : M →ₗ[A] M', g.baseChange B = f := by sorry
