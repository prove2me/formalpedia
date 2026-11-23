-- Prove2me | Theorems.Thm_GlobalTheory_LGrowth_mellin_summatory
-- name    : GlobalTheory.LGrowth.mellin_summatory
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:19.477803+00:00
-- url     : https://prove2.me/theorems/3e4a45a5-c19e-4e21-b460-76d8e99d0415
-- title:
--   LGrowth: mellin summatory
-- statement:
--   The LGrowth construction uses the mellin summatory property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtMellinSummatory.lean#L56-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableAtMellinSummatory.lean#L56-L67

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

theorem GlobalTheory.LGrowth.mellin_summatory (s : ℂ) :
    mellin (summatory f) (-s) =
      ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)) := by sorry
