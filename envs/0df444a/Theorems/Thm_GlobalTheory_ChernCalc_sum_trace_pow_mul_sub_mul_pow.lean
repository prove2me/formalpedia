-- Prove2me | Theorems.Thm_GlobalTheory_ChernCalc_sum_trace_pow_mul_sub_mul_pow
-- name    : GlobalTheory.ChernCalc.sum_trace_pow_mul_sub_mul_pow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:14.031849+00:00
-- url     : https://prove2.me/theorems/6bd46ef4-78d8-4334-a145-c0db0d1b1916
-- title:
--   Chern Calc: sum trace pow mul sub mul pow
-- statement:
--   The Chern Calc construction uses the sum trace pow mul sub mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumTracePowMulSubMulPowTelescope.lean#L5-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumTracePowMulSubMulPowTelescope.lean#L5-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumTracePowMulSubMulPowTelescope
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ChernCalc

theorem GlobalTheory.ChernCalc.sum_trace_pow_mul_sub_mul_pow (R : Type) [CommRing R] (r : Type) [Fintype r]
    [DecidableEq r] (P Q : Matrix r r R) (k : ℕ) :
    ∑ i ∈ Finset.range k, (P ^ i * (P - Q) * Q ^ (k - 1 - i)).trace
      = (P ^ k).trace - (Q ^ k).trace := by sorry
