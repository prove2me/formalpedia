-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_surj_localization_mvPolynomial_of_essFiniteType_local
-- name    : GlobalTheory.T.exists_surj_localization_mvPolynomial_of_essFiniteType_local
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:30:57.010593+00:00
-- url     : https://prove2.me/theorems/74e817fa-df38-530f-85e1-3bad86781c7a
-- title:
--   T: exists surj localization mv Polynomial of ess Finite Type local
-- statement:
--   The T construction uses the exists surj localization mv Polynomial of ess Finite Type local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSurjLocalizationMvPolynomialOfEssFiniteTypStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSurjLocalizationMvPolynomialOfEssFiniteTypStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjLocalizationMvPolynomialOfEssFiniteTyp
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjLocalizationMvPolynomialOfEssFiniteTypStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_surj_localization_mvPolynomial_of_essFiniteType_local : ∀ (Λ R : Type) [CommRing Λ] [CommRing R] [IsLocalRing R] [Algebra Λ R] [Algebra.EssFiniteType Λ R], ∃ (n : ℕ) (P : Ideal (MvPolynomial (Fin n) Λ)) (_ : P.IsPrime) (φ : Localization.AtPrime P →ₐ[Λ] R), Function.Surjective φ := by sorry
