-- Prove2me | Theorems.Thm_GlobalTheory_IntertwineAeval_intertwine_pow
-- name    : GlobalTheory.IntertwineAeval.intertwine_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:19:57.377508+00:00
-- url     : https://prove2.me/theorems/e8007153-80f8-4cdb-b797-f3bae777f02d
-- title:
--   Intertwine Aeval: intertwine pow
-- statement:
--   The Intertwine Aeval construction uses the intertwine pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IntertwineAeval.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IntertwineAeval.lean#L5-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntertwineAeval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntertwineAeval

theorem GlobalTheory.IntertwineAeval.intertwine_pow {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (r : M →ₗ[ℂ] N) {T : Module.End ℂ M} {T' : Module.End ℂ N}
    (h : ∀ v : M, r (T v) = T' (r v)) (n : ℕ) (v : M) : r ((T ^ n) v) = (T' ^ n) (r v) := by sorry
