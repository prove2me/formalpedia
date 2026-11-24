-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_isQuadraticSqrtExtension_of_not_square
-- name    : GlobalTheory.T.exists_isQuadraticSqrtExtension_of_not_square
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:36:38.430131+00:00
-- url     : https://prove2.me/theorems/6ebe820e-227f-4381-9bc6-ec9ed984488a
-- title:
--   T: exists is Quadratic Sqrt Extension of not square
-- statement:
--   The T construction uses the exists is Quadratic Sqrt Extension of not square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsQuadraticSqrtExtensionOfNotSquareStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsQuadraticSqrtExtensionOfNotSquareStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquare
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquareStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_isQuadraticSqrtExtension_of_not_square : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ := by sorry
