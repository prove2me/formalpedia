-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_two_places_of_isSquare
-- name    : GlobalTheory.QNorm.two_places_of_isSquare
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:05.769362+00:00
-- url     : https://prove2.me/theorems/b35ed985-2ebc-41ec-afa3-3c4314282883
-- title:
--   QNorm: two places of is Square
-- statement:
--   The QNorm construction uses the two places of is Square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsTwoPlacesOverOfIsSquareLocal.lean#L98-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsTwoPlacesOverOfIsSquareLocal.lean#L98-L158

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTwoPlacesOverOfIsSquareLocal
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
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.two_places_of_isSquare : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ v : HeightOneSpectrum (𝓞 F), IsSquare (algebraMap F (v.adicCompletion F) δ) → ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 F) = v ∧ w'.under (𝓞 F) = v := by sorry
