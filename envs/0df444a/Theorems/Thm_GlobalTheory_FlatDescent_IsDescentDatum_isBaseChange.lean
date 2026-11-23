-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_IsDescentDatum_isBaseChange
-- name    : GlobalTheory.FlatDescent.IsDescentDatum.isBaseChange
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:14.419442+00:00
-- url     : https://prove2.me/theorems/77c29e4f-854a-4c8e-bc93-07653f18854c
-- title:
--   Is Descent Datum: is Base Change
-- statement:
--   The Is Descent Datum construction uses the is Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueBaseChangeEqOfMem.lean#L102-L104

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

theorem GlobalTheory.FlatDescent.IsDescentDatum.isBaseChange [Module.Flat A B] {θ : N →ₗ[B] B ⊗[A] N}
    (h : IsDescentDatum θ) : IsBaseChange B (invariants θ).subtype := by sorry
