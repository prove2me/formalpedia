-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_two_places_over_of_isSquare_local
-- name    : GlobalTheory.T.exists_two_places_over_of_isSquare_local
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:37:42.307822+00:00
-- url     : https://prove2.me/theorems/99785dd2-29af-4311-8951-45183e0e6721
-- title:
--   T: exists two places over of is Square local
-- statement:
--   The T construction uses the exists two places over of is Square local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsTwoPlacesOverOfIsSquareLocalStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsTwoPlacesOverOfIsSquareLocalStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTwoPlacesOverOfIsSquareLocal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTwoPlacesOverOfIsSquareLocalStatement
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

theorem GlobalTheory.T.exists_two_places_over_of_isSquare_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ v : HeightOneSpectrum (𝓞 F), IsSquare (algebraMap F (v.adicCompletion F) δ) → ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 F) = v ∧ w'.under (𝓞 F) = v := by sorry
