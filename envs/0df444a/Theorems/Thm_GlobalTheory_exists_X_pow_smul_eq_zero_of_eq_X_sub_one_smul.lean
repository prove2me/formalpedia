-- Prove2me | Theorems.Thm_GlobalTheory_exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul
-- name    : GlobalTheory.exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:20.154291+00:00
-- url     : https://prove2.me/theorems/f820556d-d3b3-4341-9d98-3cb80eb56c51
-- title:
--   Global Theory: exists X pow smul eq zero of eq X sub one smul
-- statement:
--   The Global Theory construction uses the exists X pow smul eq zero of eq X sub one smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsXPowSmulEqZeroOfEqXSubOneSmul.lean#L110-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsXPowSmulEqZeroOfEqXSubOneSmul.lean#L110-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsXPowSmulEqZeroOfEqXSubOneSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι)
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι)

theorem GlobalTheory.exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul {n : ℤ} {z w : M} (hz : z ∈ ℳ n)
    (h : z = (X i - 1 : MvPolynomial ι R) • w) :
    ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z = 0 := by sorry
