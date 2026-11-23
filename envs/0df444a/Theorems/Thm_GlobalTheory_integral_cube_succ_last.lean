-- Prove2me | Theorems.Thm_GlobalTheory_integral_cube_succ_last
-- name    : GlobalTheory.integral_cube_succ_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:22.613316+00:00
-- url     : https://prove2.me/theorems/284961e7-345c-47d9-a126-a08c808118d8
-- title:
--   Global Theory: integral cube succ last
-- statement:
--   The Global Theory construction uses the integral cube succ last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SobolevIteratedOneParameterSubgroups.lean#L21-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SobolevIteratedOneParameterSubgroups.lean#L21-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqIntervalIntegralLeMulIntervalIntegralSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SobolevIteratedOneParameterSubgroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory

theorem GlobalTheory.integral_cube_succ_last (N : ℕ) (s : ℝ) (f : (Fin (N + 1) → ℝ) → ℝ) (hf : Continuous f) :
    IntegrableOn (fun t : Fin N → ℝ => ∫ r in Set.Icc (0 : ℝ) s, f (Fin.snoc (α := fun _ => ℝ) t r))
      (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s)) ∧
    ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s), f t =
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ∫ r in Set.Icc (0 : ℝ) s, f (Fin.snoc (α := fun _ => ℝ) t r) := by sorry
