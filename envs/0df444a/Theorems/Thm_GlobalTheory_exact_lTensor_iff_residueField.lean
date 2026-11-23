-- Prove2me | Theorems.Thm_GlobalTheory_exact_lTensor_iff_residueField
-- name    : GlobalTheory.exact_lTensor_iff_residueField
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:44.029796+00:00
-- url     : https://prove2.me/theorems/39d43be9-61da-4d57-9115-08dd63091ab0
-- title:
--   Global Theory: exact l Tensor iff residue Field
-- statement:
--   The Global Theory construction uses the exact l Tensor iff residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L27-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L27-L39

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

theorem GlobalTheory.exact_lTensor_iff_residueField (p : Ideal R) [p.IsPrime] (L : Type*) [Field L]
    [Algebra R L] (hL : RingHom.ker (algebraMap R L) = p) (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    Exact (f.lTensor L) (g.lTensor L) ↔
      Exact (f.lTensor p.ResidueField) (g.lTensor p.ResidueField) := by sorry
