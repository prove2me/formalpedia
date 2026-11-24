-- Prove2me | Theorems.Thm_GlobalTheory_NormalDescent_exists_normCoeff_not_mem
-- name    : GlobalTheory.NormalDescent.exists_normCoeff_not_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:36:22.27901+00:00
-- url     : https://prove2.me/theorems/85d21523-0376-4bdf-a241-c9215bce6007
-- title:
--   Normal Descent: exists norm Coeff not mem
-- statement:
--   The Normal Descent construction uses the exists norm Coeff not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsReversedCharpolyCoeffNotMemPrime.lean#L8-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsReversedCharpolyCoeffNotMemPrime.lean#L8-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCharpolyBaseChangeIntegrallyClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsReversedCharpolyCoeffNotMemPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent
open GlobalTheory GlobalTheory.NormalDescent

theorem GlobalTheory.NormalDescent.exists_normCoeff_not_mem {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Finite) (b : B) (hQ₀ : ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap φ = ⊥)
    (p : Ideal A) (hp : p.IsPrime) (hb : ∀ Q : Ideal B, Q.IsPrime → Q.comap φ = p → b ∉ Q) :
    ∃ k, 1 ≤ k ∧ normCoeff φ hφ b k ∉ p := by sorry
