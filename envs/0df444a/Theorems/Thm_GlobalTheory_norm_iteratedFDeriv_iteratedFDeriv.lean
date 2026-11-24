-- Prove2me | Theorems.Thm_GlobalTheory_norm_iteratedFDeriv_iteratedFDeriv
-- name    : GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:13:03.264877+00:00
-- url     : https://prove2.me/theorems/c49f985c-9a1f-4531-83aa-a13522056e81
-- title:
--   Global Theory: norm iterated FDeriv iterated FDeriv
-- statement:
--   The Global Theory construction uses the norm iterated FDeriv iterated FDeriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivIteratedFDeriv.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivIteratedFDeriv.lean#L8-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivIteratedFDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory

theorem GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (n j : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ n f) z‖ = ‖iteratedFDeriv ℝ (n + j) f z‖ := by sorry
