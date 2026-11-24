-- Prove2me | Theorems.Thm_GlobalTheory_natCard_matrices_mul_eq_zero
-- name    : GlobalTheory.natCard_matrices_mul_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:12:24.546814+00:00
-- url     : https://prove2.me/theorems/c700c1cd-7713-4a55-8d2c-f26ce456ab23
-- title:
--   Global Theory: nat Card matrices mul eq zero
-- statement:
--   The Global Theory construction uses the nat Card matrices mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/NatCardMatricesMulEqZero.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/NatCardMatricesMulEqZero.lean#L23-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_NatCardMatricesMulEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.natCard_matrices_mul_eq_zero (k : Type) [Field k] [Finite k] (m n j : ℕ)
    (A : Matrix (Fin n) (Fin n) k)
    (h : Module.finrank k (LinearMap.range A.mulVecLin) + j = n) :
    Nat.card {w : Matrix (Fin m) (Fin n) k // w * A = 0} = Nat.card k ^ (j * m) := by sorry
