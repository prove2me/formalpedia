-- Prove2me | Theorems.Thm_GlobalTheory_injective_lTensor_residueField
-- name    : GlobalTheory.injective_lTensor_residueField
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:36.321771+00:00
-- url     : https://prove2.me/theorems/478a3159-881a-45df-8b8e-2f06e5b9470a
-- title:
--   Global Theory: injective l Tensor residue Field
-- statement:
--   The Global Theory construction uses the injective l Tensor residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L135-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L135-L139

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
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
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M]
variable [Module B M] [IsScalarTower A B M] [Module.Flat A M]

theorem GlobalTheory.injective_lTensor_residueField (p : Ideal A) [p.IsPrime] :
    Function.Injective (AlgebraTensorModule.lTensor B M
      (IsScalarTower.toAlgHom A (A ⧸ p) p.ResidueField).toLinearMap) := by sorry
