-- Prove2me | Theorems.Thm_GlobalTheory_T_dw_contDiffOn_local_linear
-- name    : GlobalTheory.T.dw_contDiffOn_local_linear
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:32:51.179579+00:00
-- url     : https://prove2.me/theorems/8db910c2-9c68-45ed-9092-6b2b05d58f5f
-- title:
--   T: dw cont Diff On local linear
-- statement:
--   The T construction uses the dw cont Diff On local linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DwSmoothLocalLinearStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DwSmoothLocalLinearStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinearStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.dw_contDiffOn_local_linear : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (w : List (Fin d)), (∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ (dw w u) U) ∧ (∀ u v : E d → ℂ, Set.EqOn u v U → Set.EqOn (dw w u) (dw w v) U) ∧ (∀ u v : E d → ℂ, ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ v U → ∀ s t : ℂ, Set.EqOn (dw w (s • u + t • v)) (s • dw w u + t • dw w v) U) := by sorry
