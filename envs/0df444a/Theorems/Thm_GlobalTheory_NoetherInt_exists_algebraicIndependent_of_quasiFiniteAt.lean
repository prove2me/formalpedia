-- Prove2me | Theorems.Thm_GlobalTheory_NoetherInt_exists_algebraicIndependent_of_quasiFiniteAt
-- name    : GlobalTheory.NoetherInt.exists_algebraicIndependent_of_quasiFiniteAt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:34:46.514267+00:00
-- url     : https://prove2.me/theorems/a5c091fc-d693-42bf-9f25-24eb373f0699
-- title:
--   Noether Int: exists algebraic Independent of quasi Finite At
-- statement:
--   The Noether Int construction uses the exists algebraic Independent of quasi Finite At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L382-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L382-L398

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherInt
open MvPolynomial

theorem GlobalTheory.NoetherInt.exists_algebraicIndependent_of_quasiFiniteAt {S : Type*} [CommRing S] [IsDomain S]
    [CharZero S] (q : Ideal S) [q.IsPrime] (n : ℕ) :
    ∀ y : Fin n → S, (aeval y : MvPolynomial (Fin n) ℤ →ₐ[ℤ] S).toRingHom.QuasiFiniteAt q →
    ∃ (r : ℕ) (y' : Fin r → S), AlgebraicIndependent ℤ y' ∧
      (aeval y' : MvPolynomial (Fin r) ℤ →ₐ[ℤ] S).toRingHom.QuasiFiniteAt q := by sorry
