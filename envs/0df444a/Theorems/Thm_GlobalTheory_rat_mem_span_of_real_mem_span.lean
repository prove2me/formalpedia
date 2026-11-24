-- Prove2me | Theorems.Thm_GlobalTheory_rat_mem_span_of_real_mem_span
-- name    : GlobalTheory.rat_mem_span_of_real_mem_span
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:16:49.108488+00:00
-- url     : https://prove2.me/theorems/a4851271-7b33-47aa-a72a-0e56c6aa9fb4
-- title:
--   Global Theory: rat mem span of real mem span
-- statement:
--   The Global Theory construction uses the rat mem span of real mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RatMemSpanOfRealMemSpanFin.lean#L6-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RatMemSpanOfRealMemSpanFin.lean#L6-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RatMemSpanOfRealMemSpanFin
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

theorem GlobalTheory.rat_mem_span_of_real_mem_span (k r : ℕ) (w : Fin k → Fin r → ℚ) (v : Fin r → ℚ)
    (hv : (fun j => ((v j : ℚ) : ℝ)) ∈ Submodule.span ℝ (Set.range fun i j => ((w i j : ℚ) : ℝ))) :
    v ∈ Submodule.span ℚ (Set.range w) := by sorry
