-- Prove2me | Theorems.Thm_GlobalTheory_Chow_exists_prime_saturation_generic_section
-- name    : GlobalTheory.Chow.exists_prime_saturation_generic_section
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:24.421588+00:00
-- url     : https://prove2.me/theorems/1a518e8f-6ff4-5dc4-aa86-3719ba503476
-- title:
--   Chow: exists prime saturation generic section
-- statement:
--   The Chow construction uses the exists prime saturation generic section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimeSaturationGenericHyperplaneSection.lean#L60-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimeSaturationGenericHyperplaneSection.lean#L60-L184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeSaturationGenericHyperplaneSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow

theorem GlobalTheory.Chow.exists_prime_saturation_generic_section (K L : Type) [Field K] [Field L] (N : ℕ)
    [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L]
    [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L]
    (P : Ideal (MvPolynomial (Fin N) K)) (hprime : P.IsPrime)
    (hP : ∀ u : Fin N → AlgebraicClosure K, ∃ y : Fin N → AlgebraicClosure K,
      y ≠ 0 ∧ (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, u j * y j = 0) :
    ∃ Q : Ideal (MvPolynomial (Fin N) L), Q.IsPrime ∧
      P.map (MvPolynomial.map (algebraMap K L) :
          MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
        Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
          MvPolynomial (Fin N) L)} ≤ Q ∧
      ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈
        P.map (MvPolynomial.map (algebraMap K L) :
          MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔
        Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
          MvPolynomial (Fin N) L)} := by sorry
