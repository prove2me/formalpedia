-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_quasi_finite_polynomial_map
-- name    : GlobalTheory.T.exists_quasi_finite_polynomial_map
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:38:20.223888+00:00
-- url     : https://prove2.me/theorems/1b0f9d72-cc1f-4c91-bc40-500259c3974d
-- title:
--   T: exists quasi finite polynomial map
-- statement:
--   The T construction uses the exists quasi finite polynomial map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMapStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMapStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMapStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_quasi_finite_polynomial_map : ∀ (S : Type) [CommRing S] [IsDomain S] [CharZero S] [Algebra.FiniteType ℤ S] (𝔮 : Ideal S) [𝔮.IsPrime], ∃ (r : ℕ) (y : Fin r → S), AlgebraicIndependent ℤ y ∧ @Algebra.QuasiFiniteAt (MvPolynomial (Fin r) ℤ) S _ _ (MvPolynomial.aeval y : MvPolynomial (Fin r) ℤ →ₐ[ℤ] S).toRingHom.toAlgebra 𝔮 _ := by sorry
