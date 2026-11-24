-- Prove2me | Theorems.Thm_GlobalTheory_LGrowth_measurable_summatory
-- name    : GlobalTheory.LGrowth.measurable_summatory
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:55:50.095267+00:00
-- url     : https://prove2.me/theorems/038a94f2-8517-40c4-af27-63c125c7c9ee
-- title:
--   LGrowth: measurable summatory
-- statement:
--   The LGrowth construction uses the measurable summatory property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtMellinSummatory.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtMellinSummatory.lean#L50-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtMellinSummatory
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LGrowth
open Filter Topology Asymptotics
variable {f : ℕ → ℂ} {C : ℝ}

theorem GlobalTheory.LGrowth.measurable_summatory (f : ℕ → ℂ) : Measurable (summatory f) := by sorry
