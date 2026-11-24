-- Prove2me | Theorems.Thm_GlobalTheory_RowDet_minor_isRelPrime
-- name    : GlobalTheory.RowDet.minor_isRelPrime
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:30:17.679133+00:00
-- url     : https://prove2.me/theorems/370d3ca8-f075-4a09-9f16-f40cc9f49739
-- title:
--   Row Det: minor is Rel Prime
-- statement:
--   The Row Det construction uses the minor is Rel Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IrreducibleDetOfIsRelPrime.lean#L121-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IrreducibleDetOfIsRelPrime.lean#L121-L136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.RowDet

theorem GlobalTheory.RowDet.minor_isRelPrime {R σ : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (e : Fin (n + 1) × Fin (n + 1) → σ) (he : Function.Injective e) :
    ((Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).submatrix
        Fin.castSucc Fin.castSucc).det ≠ 0 ∧
    IsRelPrime ((Matrix.of fun i k : Fin (n + 1) =>
        (X (e (i, k)) : MvPolynomial σ R)).submatrix Fin.castSucc Fin.castSucc).det
      (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det := by sorry
