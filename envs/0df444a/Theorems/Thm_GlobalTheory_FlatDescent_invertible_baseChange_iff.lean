-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_invertible_baseChange_iff
-- name    : GlobalTheory.FlatDescent.invertible_baseChange_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:32:18.00702+00:00
-- url     : https://prove2.me/theorems/3d74e74d-b9cb-45a4-b8c6-2cbd0c2aa929
-- title:
--   Flat Descent: invertible base Change iff
-- statement:
--   The Flat Descent construction uses the invertible base Change iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean#L217-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean#L217-L219

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
variable (B)

theorem GlobalTheory.FlatDescent.invertible_baseChange_iff [Module.FaithfullyFlat A B] (M : Type*) [AddCommGroup M]
    [Module A M] : Module.Invertible B (B ⊗[A] M) ↔ Module.Invertible A M := by sorry
