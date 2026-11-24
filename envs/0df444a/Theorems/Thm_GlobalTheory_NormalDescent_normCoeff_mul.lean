-- Prove2me | Theorems.Thm_GlobalTheory_NormalDescent_normCoeff_mul
-- name    : GlobalTheory.NormalDescent.normCoeff_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:35:47.41583+00:00
-- url     : https://prove2.me/theorems/57297d98-78db-450b-a838-0424330c15a6
-- title:
--   Normal Descent: norm Coeff mul
-- statement:
--   The Normal Descent construction uses the norm Coeff mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ReversedCharpolyCoeffInDomainMul.lean#L74-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ReversedCharpolyCoeffInDomainMul.lean#L74-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ReversedCharpolyCoeffInDomainMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Polynomial TensorProduct
open GlobalTheory GlobalTheory.NormalDescent

theorem GlobalTheory.NormalDescent.normCoeff_mul : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (u : A) (b : B) (k : ℕ), normCoeff φ hφ (φ u * b) k = u ^ k * normCoeff φ hφ b k := by sorry
