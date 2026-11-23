-- Prove2me | Theorems.Thm_GlobalTheory_FibLine_lintegral_comp_fsDens
-- name    : GlobalTheory.FibLine.lintegral_comp_fsDens
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:10.814677+00:00
-- url     : https://prove2.me/theorems/213ccdc2-8d8c-4268-80f3-f654044b24ce
-- title:
--   Fib Line: lintegral comp fs Dens
-- statement:
--   The Fib Line construction uses the lintegral comp fs Dens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StereographicMeasureChange.lean#L12-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StereographicMeasureChange.lean#L12-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StereographicMeasureChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FibLine
open Real Set

theorem GlobalTheory.FibLine.lintegral_comp_fsDens :
    ∀ g : ℝ → ℝ≥0∞, Measurable g →
    ∫⁻ x : ℂ, g (1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)) =
      ∫⁻ t in Set.Ioo (0:ℝ) 1, g t := by sorry
