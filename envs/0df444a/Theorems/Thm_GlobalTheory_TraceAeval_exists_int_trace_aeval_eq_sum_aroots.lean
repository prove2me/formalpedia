-- Prove2me | Theorems.Thm_GlobalTheory_TraceAeval_exists_int_trace_aeval_eq_sum_aroots
-- name    : GlobalTheory.TraceAeval.exists_int_trace_aeval_eq_sum_aroots
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:42:31.294622+00:00
-- url     : https://prove2.me/theorems/05fa0f0c-becf-4b3d-86e3-a11439979298
-- title:
--   Trace Aeval: exists int trace aeval eq sum aroots
-- statement:
--   The Trace Aeval construction uses the exists int trace aeval eq sum aroots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TracePowerSumModEq.lean#L133-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TracePowerSumModEq.lean#L133-L156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TracePowerSumModEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TraceAeval
open Module

theorem GlobalTheory.TraceAeval.exists_int_trace_aeval_eq_sum_aroots :
    ∀ (χ p : Polynomial ℤ), χ.Monic → ∃ s : ℤ, (s : ℂ) = ((χ.aroots ℂ).map fun z => Polynomial.aeval z p).sum ∧ ∀ (n M : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod M)), B.charpoly = χ.map (Int.castRingHom (ZMod M)) → (Polynomial.aeval B p).trace = (s : ZMod M) := by sorry
