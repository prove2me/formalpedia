-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_bijective_toInvariants
-- name    : GlobalTheory.FlatDescent.bijective_toInvariants
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:23.138964+00:00
-- url     : https://prove2.me/theorems/c09ac579-59b9-4ad9-aa4e-a61063be7f82
-- title:
--   Flat Descent: bijective to Invariants
-- statement:
--   The Flat Descent construction uses the bijective to Invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean#L116-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean#L116-L125

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
variable (B) (M : Type*) [AddCommGroup M] [Module A M]

theorem GlobalTheory.FlatDescent.bijective_toInvariants [Module.FaithfullyFlat A B] :
    Function.Bijective (toInvariants (A := A) B M) := by sorry
