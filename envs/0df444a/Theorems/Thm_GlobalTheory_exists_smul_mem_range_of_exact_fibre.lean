-- Prove2me | Theorems.Thm_GlobalTheory_exists_smul_mem_range_of_exact_fibre
-- name    : GlobalTheory.exists_smul_mem_range_of_exact_fibre
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:00:06.131011+00:00
-- url     : https://prove2.me/theorems/eebd0f46-5f67-4c75-b231-18ebe0d655f3
-- title:
--   Global Theory: exists smul mem range of exact fibre
-- statement:
--   The Global Theory construction uses the exists smul mem range of exact fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulHomologyEqZeroOfAcyclicFibre.lean#L11-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulHomologyEqZeroOfAcyclicFibre.lean#L11-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulHomologyEqZeroOfAcyclicFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct Function
open GlobalTheory

theorem GlobalTheory.exists_smul_mem_range_of_exact_fibre {R : Type*} [CommRing R] {A B C : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [Module.Finite R B] [Module.Projective R B] [Module.Finite R C] [Module.Projective R C]
    (K : Type*) [Field K] [Algebra R K] {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    (h : Exact (f.lTensor K) (g.lTensor K)) (b : B) (hb : g b = 0) :
    ∃ r : R, algebraMap R K r ≠ 0 ∧ r • b ∈ LinearMap.range f := by sorry
