-- Prove2me | Theorems.Thm_GlobalTheory_exists_primeInvolution_of_ringInvolution
-- name    : GlobalTheory.exists_primeInvolution_of_ringInvolution
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:20:47.841408+00:00
-- url     : https://prove2.me/theorems/0243beae-b02f-5e6e-ad79-478c9497177a
-- title:
--   Global Theory: exists prime Involution of ring Involution
-- statement:
--   The Global Theory construction uses the exists prime Involution of ring Involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsPrimeInvolutionOfRingInvolution.lean#L8-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsPrimeInvolutionOfRingInvolution.lean#L8-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPrimeInvolutionOfRingInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
open GlobalTheory

theorem GlobalTheory.exists_primeInvolution_of_ringInvolution {R : Type} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] (s : R ≃+* R) (hs : ∀ x, s (s x) = x) :
    ∃ c : HeightOneSpectrum R ≃ HeightOneSpectrum R, (∀ P, c (c P) = P) ∧
      (∀ P, Ideal.absNorm (c P).asIdeal = Ideal.absNorm P.asIdeal) ∧
      (∀ P x, s x ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧
      (∀ P x, s x ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2) := by sorry
