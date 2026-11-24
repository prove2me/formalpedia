-- Prove2me | Theorems.Thm_GlobalTheory_TraceDetSplit_trace_mul_eq
-- name    : GlobalTheory.TraceDetSplit.trace_mul_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:10:42.65218+00:00
-- url     : https://prove2.me/theorems/19e4f9bf-38f6-492a-ae1a-8ea185a9e4c6
-- title:
--   Trace Det Split: trace mul eq
-- statement:
--   The Trace Det Split construction uses the trace mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyLeftMulBasis.lean#L74-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyLeftMulBasis.lean#L74-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TraceDetSplit

theorem GlobalTheory.TraceDetSplit.trace_mul_eq {E A : Type} [Field E] [CommRing A] [Algebra E A] {n : ℕ} (x : Fin n → A)
    (h : A) (w : Module.Basis (Fin n) E A) :
    (Matrix.of fun k l : Fin n => Algebra.trace E A (x k * h * w l))
      = (Matrix.of fun k l : Fin n => Algebra.trace E A (x k * w l)) * Algebra.leftMulMatrix w h := by sorry
