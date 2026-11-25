-- Prove2me | Theorems.Thm_GlobalTheory_NoetherInt_exists_quasiFiniteAt_of_not_injective
-- name    : GlobalTheory.NoetherInt.exists_quasiFiniteAt_of_not_injective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:01.144805+00:00
-- url     : https://prove2.me/theorems/1a01f556-7882-451d-94fe-fd983b00695a
-- title:
--   Noether Int: exists quasi Finite At of not injective
-- statement:
--   The Noether Int construction uses the exists quasi Finite At of not injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L301-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L301-L380

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

theorem GlobalTheory.NoetherInt.exists_quasiFiniteAt_of_not_injective {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    (q : Ideal S) [q.IsPrime] {n : ℕ} (y : Fin (n + 1) → S)
    (h : (aeval y : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S).toRingHom.QuasiFiniteAt q)
    (hy : ¬ Function.Injective (aeval y : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S)) :
    ∃ y' : Fin n → S, (aeval y' : MvPolynomial (Fin n) ℤ →ₐ[ℤ] S).toRingHom.QuasiFiniteAt q := by sorry
