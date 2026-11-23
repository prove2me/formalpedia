-- Prove2me | Theorems.Thm_GlobalTheory_LGrowth_summatory_eq_zero
-- name    : GlobalTheory.LGrowth.summatory_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:25.404686+00:00
-- url     : https://prove2.me/theorems/95b0f599-676d-4bb8-88c6-3eca52f60574
-- title:
--   LGrowth: summatory eq zero
-- statement:
--   The LGrowth construction uses the summatory eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtMellinSummatory.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtMellinSummatory.lean#L53-L54

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

theorem GlobalTheory.LGrowth.summatory_eq_zero {t : ℝ} (ht : t < 1) : summatory f t = 0 := by sorry
