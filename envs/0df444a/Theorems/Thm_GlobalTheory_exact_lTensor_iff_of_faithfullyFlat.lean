-- Prove2me | Theorems.Thm_GlobalTheory_exact_lTensor_iff_of_faithfullyFlat
-- name    : GlobalTheory.exact_lTensor_iff_of_faithfullyFlat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:20:09.812598+00:00
-- url     : https://prove2.me/theorems/fe538ece-91c4-4009-96d6-fd4eedbfeb24
-- title:
--   Global Theory: exact l Tensor iff of faithfully Flat
-- statement:
--   The Global Theory construction uses the exact l Tensor iff of faithfully Flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L13-L25

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

theorem GlobalTheory.exact_lTensor_iff_of_faithfullyFlat (k L : Type*) [CommRing k] [CommRing L] [Algebra R k]
    [Algebra R L] [Algebra k L] [IsScalarTower R k L] [Module.FaithfullyFlat k L]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    Exact (f.lTensor L) (g.lTensor L) ↔ Exact (f.lTensor k) (g.lTensor k) := by sorry
