-- Prove2me | Theorems.Thm_GlobalTheory_IntegralTrace_isIntegral_trace
-- name    : GlobalTheory.IntegralTrace.isIntegral_trace
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:20:12.598867+00:00
-- url     : https://prove2.me/theorems/ef96cc17-0120-4cbf-ab4e-69f3769e4d13
-- title:
--   Integral Trace: is Integral trace
-- statement:
--   The Integral Trace construction uses the is Integral trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMonicAevalEqZero.lean#L44-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMonicAevalEqZero.lean#L44-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMonicAevalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.IntegralTrace
open Polynomial

theorem GlobalTheory.IntegralTrace.isIntegral_trace {E : Type u_1} [inst : Field E] [NumberField E] (_φ : E →+* ℂ) {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.FG L)
    (hspan : Submodule.span E (↑L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, Matrix.mulVec M x ∈ L) :
    IsIntegral ℤ (Matrix.trace M) := by sorry
