-- Prove2me | Theorems.Thm_GlobalTheory_IsoIdem_eq_zero_of_pow_eq_zero
-- name    : GlobalTheory.IsoIdem.eq_zero_of_pow_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:20:59.432811+00:00
-- url     : https://prove2.me/theorems/792f7e57-c27d-45d5-a676-6d19f28952d5
-- title:
--   Iso Idem: eq zero of pow eq zero
-- statement:
--   The Iso Idem construction uses the eq zero of pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIsotropicIdempotentCentralizerHermitian.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIsotropicIdempotentCentralizerHermitian.lean#L8-L19

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

theorem GlobalTheory.IsoIdem.eq_zero_of_pow_eq_zero {E : Type} [Field E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (hs : A.charpoly.Separable) (y : Matrix (Fin r) (Fin r) E) (hy : y * A = A * y) (k : ℕ)
    (hk : y ^ k = 0) : y = 0 := by sorry
