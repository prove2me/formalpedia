-- Prove2me | Theorems.Thm_GlobalTheory_TwistDual_mulVec_surjective
-- name    : GlobalTheory.TwistDual.mulVec_surjective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:12:59.056135+00:00
-- url     : https://prove2.me/theorems/6c613672-451b-440d-804e-91b49c4b84de
-- title:
--   Twist Dual: mul Vec surjective
-- statement:
--   The Twist Dual construction uses the mul Vec surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FromColsMulVecEqZero.lean#L35-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FromColsMulVecEqZero.lean#L35-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FromColsMulVecEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TwistDual
open Matrix
variable {E : Type} [Field E] [StarRing E] [CharZero E]

theorem GlobalTheory.TwistDual.mulVec_surjective {n r m : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : Gᴴ = G) (hGd : G.det ≠ 0)
    {C : Matrix (Fin n) (Fin r) E} {B : Matrix (Fin n) (Fin m) E} (hC : LinearIndependent E Cᵀ)
    (hBB : (Bᴴ * G * B).det ≠ 0) (hCB : Cᴴ * G * B = 0) :
    Function.Surjective ((Matrix.fromCols C B)ᴴ * G).mulVecLin := by sorry
