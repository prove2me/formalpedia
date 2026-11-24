-- Prove2me | Theorems.Thm_GlobalTheory_CuspFormEvaluationComplement_main
-- name    : GlobalTheory.CuspFormEvaluationComplement.main
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:29:23.142532+00:00
-- url     : https://prove2.me/theorems/d2c416ea-335c-4d29-8bd8-0aae4f26e3bb
-- title:
--   Cusp Form Evaluation Complement: main
-- statement:
--   The Cusp Form Evaluation Complement construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ImportsAlt.lean#L5-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ImportsAlt.lean#L5-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CuspFormEvaluationComplement

theorem GlobalTheory.CuspFormEvaluationComplement.main : ∀ (s : Multiset ℂ) {t : ℝ}, (0 : ℝ) ≤ t → (∀ μ ∈ s, ‖μ - (1 : ℂ)‖ ≤ t) →
    ‖Multiset.prod s - (1 : ℂ)‖ ≤ Real.exp ((↑(Multiset.card s) : ℝ) * t) - (1 : ℝ) := by sorry
