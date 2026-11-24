-- Prove2me | Theorems.Thm_GlobalTheory_IntegralTrace_exists_monic_aeval_eq_zero
-- name    : GlobalTheory.IntegralTrace.exists_monic_aeval_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:20:01.026061+00:00
-- url     : https://prove2.me/theorems/7d16d040-83c7-43a8-ae56-e9b7d1e00c1c
-- title:
--   Integral Trace: exists monic aeval eq zero
-- statement:
--   The Integral Trace construction uses the exists monic aeval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMonicAevalEqZero.lean#L9-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMonicAevalEqZero.lean#L9-L42

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

theorem GlobalTheory.IntegralTrace.exists_monic_aeval_eq_zero {R E : Type*} [CommRing R] [Field E] [Algebra R E] {n : ℕ}
    (L : Submodule R (Fin n → E)) (hL : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, M.mulVec x ∈ L) :
    ∃ p : R[X], p.Monic ∧ aeval M (p.map (algebraMap R E)) = 0 := by sorry
