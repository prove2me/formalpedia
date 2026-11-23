-- Prove2me | Theorems.Thm_GlobalTheory_split_injective_of_forall_lTensor_residueField_injective
-- name    : GlobalTheory.split_injective_of_forall_lTensor_residueField_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:38.877131+00:00
-- url     : https://prove2.me/theorems/13f40d57-ad76-4624-83c0-84015be87c8c
-- title:
--   Global Theory: split injective of forall l Tensor residue Field injective
-- statement:
--   The Global Theory construction uses the split injective of forall l Tensor residue Field injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L41-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L41-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Function
open GlobalTheory
variable {R : Type*} [CommRing R] {A B C : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

theorem GlobalTheory.split_injective_of_forall_lTensor_residueField_injective [Module.Finite R B]
    [Module.Finite R C] [Module.Projective R C] (l : B →ₗ[R] C)
    (h : ∀ (m : Ideal R) [m.IsMaximal], Injective (l.lTensor m.ResidueField)) :
    ∃ r : C →ₗ[R] B, r ∘ₗ l = LinearMap.id := by sorry
