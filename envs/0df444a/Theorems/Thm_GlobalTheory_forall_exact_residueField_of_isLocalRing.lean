-- Prove2me | Theorems.Thm_GlobalTheory_forall_exact_residueField_of_isLocalRing
-- name    : GlobalTheory.forall_exact_residueField_of_isLocalRing
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:52:00.457319+00:00
-- url     : https://prove2.me/theorems/5165084d-0d92-4fb8-bd32-51d4de55c95f
-- title:
--   Global Theory: forall exact residue Field of is Local Ring
-- statement:
--   The Global Theory construction uses the forall exact residue Field of is Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L130-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L130-L135

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

theorem GlobalTheory.forall_exact_residueField_of_isLocalRing [IsLocalRing R] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h : Exact (f.lTensor (IsLocalRing.ResidueField R)) (g.lTensor (IsLocalRing.ResidueField R)))
    (m : Ideal R) [m.IsMaximal] :
    Exact (f.lTensor m.ResidueField) (g.lTensor m.ResidueField) := by sorry
