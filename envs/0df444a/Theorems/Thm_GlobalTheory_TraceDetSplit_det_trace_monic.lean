-- Prove2me | Theorems.Thm_GlobalTheory_TraceDetSplit_det_trace_monic
-- name    : GlobalTheory.TraceDetSplit.det_trace_monic
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:11:04.939641+00:00
-- url     : https://prove2.me/theorems/9425e33e-ca50-40d8-a973-bf221cda5959
-- title:
--   Trace Det Split: det trace monic
-- statement:
--   The Trace Det Split construction uses the det trace monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyLeftMulBasis.lean#L41-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyLeftMulBasis.lean#L41-L66

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

theorem GlobalTheory.TraceDetSplit.det_trace_monic {E A : Type} [Field E] [CommRing A] [Algebra E A] {n : ℕ} (g : A)
    (e : Fin n → A) (q : Fin n → E[X]) (hd : ∀ k, (q k).natDegree = k) (hm : ∀ k, (q k).Monic) :
    (Matrix.of fun k l : Fin n => Algebra.trace E A (g ^ (k : ℕ) * e l)).det
      = (Matrix.of fun k l : Fin n => Algebra.trace E A (aeval g (q k) * e l)).det := by sorry
