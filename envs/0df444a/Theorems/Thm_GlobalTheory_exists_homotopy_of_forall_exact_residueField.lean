-- Prove2me | Theorems.Thm_GlobalTheory_exists_homotopy_of_forall_exact_residueField
-- name    : GlobalTheory.exists_homotopy_of_forall_exact_residueField
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:00.080786+00:00
-- url     : https://prove2.me/theorems/dd7be230-a8d9-4d6d-a9ac-d8c25b46d84c
-- title:
--   Global Theory: exists homotopy of forall exact residue Field
-- statement:
--   The Global Theory construction uses the exists homotopy of forall exact residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L104-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L104-L128

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

theorem GlobalTheory.exists_homotopy_of_forall_exact_residueField [Module.Finite R B] [Module.Projective R B]
    [Module.Finite R C] [Module.Projective R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Exact (f.lTensor m.ResidueField) (g.lTensor m.ResidueField)) :
    ∃ (s : B →ₗ[R] A) (t : C →ₗ[R] B), f ∘ₗ s + t ∘ₗ g = LinearMap.id := by sorry
