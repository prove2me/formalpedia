-- Prove2me | Theorems.Thm_GlobalTheory_natCast_mul_coeff_charpolyRev
-- name    : GlobalTheory.natCast_mul_coeff_charpolyRev
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:39.830395+00:00
-- url     : https://prove2.me/theorems/f13e230b-646d-47db-8381-92a540f2f2c8
-- title:
--   Global Theory: nat Cast mul coeff charpoly Rev
-- statement:
--   The Global Theory construction uses the nat Cast mul coeff charpoly Rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NatCastMulCoeffCharpolyRev.lean#L6-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NatCastMulCoeffCharpolyRev.lean#L6-L19

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NatCastMulCoeffCharpolyRev
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.natCast_mul_coeff_charpolyRev {R : Type} [CommRing R] {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R) (k : ℕ) :
    (k : R) * M.charpolyRev.coeff k =
      -∑ i ∈ Finset.range k, (M ^ (i + 1)).trace * M.charpolyRev.coeff (k - 1 - i) := by sorry
