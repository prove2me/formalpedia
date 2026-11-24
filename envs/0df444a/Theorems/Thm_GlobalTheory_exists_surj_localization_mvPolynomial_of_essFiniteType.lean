-- Prove2me | Theorems.Thm_GlobalTheory_exists_surj_localization_mvPolynomial_of_essFiniteType
-- name    : GlobalTheory.exists_surj_localization_mvPolynomial_of_essFiniteType
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:17.627814+00:00
-- url     : https://prove2.me/theorems/0af645bf-adf7-407f-ba4d-6a45d3b24608
-- title:
--   Global Theory: exists surj localization mv Polynomial of ess Finite Type
-- statement:
--   The Global Theory construction uses the exists surj localization mv Polynomial of ess Finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSurjLocalizationMvPolynomialOfEssFiniteTyp.lean#L6-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSurjLocalizationMvPolynomialOfEssFiniteTyp.lean#L6-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjLocalizationMvPolynomialOfEssFiniteTyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_surj_localization_mvPolynomial_of_essFiniteType :
    ∀ (Λ R : Type) [CommRing Λ] [CommRing R] [IsLocalRing R] [Algebra Λ R]
      [Algebra.EssFiniteType Λ R], ∃ (n : ℕ) (P : Ideal (MvPolynomial (Fin n) Λ)) (_ : P.IsPrime)
      (φ : Localization.AtPrime P →ₐ[Λ] R), Function.Surjective φ := by sorry
