-- Prove2me | Theorems.Thm_GlobalTheory_NoetherInt_exists_primitive_of_aeval_eq_zero
-- name    : GlobalTheory.NoetherInt.exists_primitive_of_aeval_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:34:54.161275+00:00
-- url     : https://prove2.me/theorems/5df93091-6b86-4f38-87f8-7361b0261d41
-- title:
--   Noether Int: exists primitive of aeval eq zero
-- statement:
--   The Noether Int construction uses the exists primitive of aeval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L245-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L245-L285

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

theorem GlobalTheory.NoetherInt.exists_primitive_of_aeval_eq_zero {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    {n : ℕ} (y : Fin n → S) (g : MvPolynomial (Fin n) ℤ) (hg0 : g ≠ 0)
    (hg : aeval y g = 0) (I : Ideal ℤ) (hI : I ≠ ⊤) :
    ∃ g₀ : MvPolynomial (Fin n) ℤ, aeval y g₀ = 0 ∧ ∃ v, g₀.coeff v ∉ I := by sorry
