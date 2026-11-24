-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_exists_place_isSquare_and_not_isSquare
-- name    : GlobalTheory.QNorm.exists_place_isSquare_and_not_isSquare
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:08:25.417911+00:00
-- url     : https://prove2.me/theorems/b10a9979-b510-4826-8202-8909f2b25d31
-- title:
--   QNorm: exists place is Square and not is Square
-- statement:
--   The QNorm construction uses the exists place is Square and not is Square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsPlaceIsSquareAndNotIsSquare.lean#L16-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsPlaceIsSquareAndNotIsSquare.lean#L16-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPlaceNotIsSquareAdicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRingHomAdicCompletionUnder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareMulOfNonsquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPlaceIsSquareAndNotIsSquare
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

theorem GlobalTheory.QNorm.exists_place_isSquare_and_not_isSquare :
    ∀ (F : Type) [Field F] [NumberField F] (δ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), δ ≠ 0 → u ≠ 0 → ¬ IsSquare δ → ¬ IsSquare u → ¬ IsSquare (u * δ) → ∃ v, v ∉ S₀ ∧ IsSquare (algebraMap F (v.adicCompletion F) δ) ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) u) := by sorry
