-- Prove2me | Theorems.Thm_GlobalTheory_IsoIdem_exists_pow_mul_eq
-- name    : GlobalTheory.IsoIdem.exists_pow_mul_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:21:20.252345+00:00
-- url     : https://prove2.me/theorems/72601dc2-a745-424b-a82b-c469655173b4
-- title:
--   Iso Idem: exists pow mul eq
-- statement:
--   The Iso Idem construction uses the exists pow mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIsotropicIdempotentCentralizerHermitian.lean#L21-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIsotropicIdempotentCentralizerHermitian.lean#L21-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommuteOfCommuteSeparableCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsotropicIdempotentCentralizerHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.IsoIdem

theorem GlobalTheory.IsoIdem.exists_pow_mul_eq {E : Type} [Field E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (hs : A.charpoly.Separable) (z : Matrix (Fin r) (Fin r) E) (hz : z * A = A * z) :
    ∃ n : ℕ, ∃ w : Matrix (Fin r) (Fin r) E, w * A = A * w ∧ z ^ (n + 1) * w = z ^ n := by sorry
