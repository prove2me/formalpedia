-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_existsUnique_baseChange_eq_of_mem
-- name    : GlobalTheory.FlatDescent.existsUnique_baseChange_eq_of_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:33:01.211991+00:00
-- url     : https://prove2.me/theorems/2f8d354a-d835-40af-bf5b-ba9ecf7a2224
-- title:
--   Flat Descent: exists Unique base Change eq of mem
-- statement:
--   The Flat Descent construction uses the exists Unique base Change eq of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean#L168-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean#L168-L181

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

theorem GlobalTheory.FlatDescent.existsUnique_baseChange_eq_of_mem [Module.FaithfullyFlat A B]
    (f : B ⊗[A] M →ₗ[B] B ⊗[A] M') (hf : ∀ m : M, f (1 ⊗ₜ m) ∈ invariants (canonical B M')) :
    ∃! g : M →ₗ[A] M', g.baseChange B = f := by sorry
