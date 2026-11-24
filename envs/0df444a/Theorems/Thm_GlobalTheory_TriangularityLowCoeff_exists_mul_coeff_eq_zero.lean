-- Prove2me | Theorems.Thm_GlobalTheory_TriangularityLowCoeff_exists_mul_coeff_eq_zero
-- name    : GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:12:25.680564+00:00
-- url     : https://prove2.me/theorems/72ec1c83-e70b-4593-88b7-676c67f22ebc
-- title:
--   Triangularity Low Coeff: exists mul coeff eq zero
-- statement:
--   The Triangularity Low Coeff construction uses the exists mul coeff eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffAnnihilatedOfAevalMemKerPow.lean#L149-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffAnnihilatedOfAevalMemKerPow.lean#L149-L195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TriangularityLowCoeff
open MvPolynomial

theorem GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero (d N : ℕ) : ∃ K : ℕ, 0 < K ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    (ε : B →ₐ[R] R) (y : Fin d → B) (D : Fin d → Derivation R B B), (∀ i, ε (y i) = 0) →
    (∀ i j, ε (D i (y j)) = if i = j then 1 else 0) → ∀ P : MvPolynomial (Fin d) R,
    (∀ α : Fin d →₀ ℕ, N ≤ α.degree → MvPolynomial.coeff α P = 0) →
    MvPolynomial.aeval y P ∈ RingHom.ker ε ^ N → ∀ α, (K : R) * MvPolynomial.coeff α P = 0 := by sorry
