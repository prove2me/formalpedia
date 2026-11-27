-- Prove2me | Theorems.Thm_GlobalTheory_T_rat_mem_span_of_real_mem_span_fin
-- name    : GlobalTheory.T.rat_mem_span_of_real_mem_span_fin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:42.541666+00:00
-- url     : https://prove2.me/theorems/0fb5bcf6-6847-59de-8437-f24b11b816dd
-- title:
--   T: rat mem span of real mem span fin
-- statement:
--   The T construction uses the rat mem span of real mem span fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RatMemSpanOfRealMemSpanFinStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RatMemSpanOfRealMemSpanFinStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RatMemSpanOfRealMemSpanFin
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RatMemSpanOfRealMemSpanFinStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.rat_mem_span_of_real_mem_span_fin : ∀ (k r : ℕ) (w : Fin k → Fin r → ℚ) (v : Fin r → ℚ), (fun j => ((v j : ℚ) : ℝ)) ∈ Submodule.span ℝ (Set.range fun i j => ((w i j : ℚ) : ℝ)) → v ∈ Submodule.span ℚ (Set.range w) := by sorry
