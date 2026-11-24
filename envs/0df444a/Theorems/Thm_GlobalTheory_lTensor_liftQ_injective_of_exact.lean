-- Prove2me | Theorems.Thm_GlobalTheory_lTensor_liftQ_injective_of_exact
-- name    : GlobalTheory.lTensor_liftQ_injective_of_exact
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:02:14.432111+00:00
-- url     : https://prove2.me/theorems/47a84041-2f5d-4fd6-90f5-7207014ac8e0
-- title:
--   Global Theory: l Tensor lift Q injective of exact
-- statement:
--   The Global Theory construction uses the l Tensor lift Q injective of exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L92-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L92-L102

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

theorem GlobalTheory.lTensor_liftQ_injective_of_exact (N : Type*) [AddCommGroup N] [Module R N]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : LinearMap.range f ≤ LinearMap.ker g)
    (h : Exact (f.lTensor N) (g.lTensor N)) :
    Injective (((LinearMap.range f).liftQ g hfg).lTensor N) := by sorry
