-- Prove2me | Theorems.Thm_GlobalTheory_X_smul_mem_gr
-- name    : GlobalTheory.X_smul_mem_gr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:58.374561+00:00
-- url     : https://prove2.me/theorems/7adb9c0a-ca08-4760-8958-79b16350f0e1
-- title:
--   Global Theory: X smul mem gr
-- statement:
--   The Global Theory construction uses the X smul mem gr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L102-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type*} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]

theorem GlobalTheory.X_smul_mem_gr (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] (i : ι) (n : ℤ) (m : M)
    (hm : m ∈ ℳ n) : (X i : MvPolynomial ι R) • m ∈ ℳ (n + 1) := by sorry
