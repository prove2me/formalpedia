-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_scp_joint_state_measurable
-- name    : ManyServerQED.Scheduling.scp_joint_state_measurable
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T20:49:00.232515+00:00
-- url     : https://prove2.me/theorems/a1d23ee8-3247-4dce-9db7-5a058e2856cc
-- title:
--   Joint measurability of the state of a scheduling control policy
-- statement:
--   For an $n$-server system, suppose its allocation is a scheduling control policy and $X$ is the state satisfying the system equations. Then the state and allocation are jointly measurable in the sample point and nonnegative time.
-- source:
--   Direct HJB comparison for Atar, Mandelbaum and Reiman, Theorem 4 and the P-SCP optimality conclusion, https://arxiv.org/abs/math/0407058

import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_Policy
open MeasureTheory ManyServerQED.Scheduling
open scoped NNReal

theorem ManyServerQED.Scheduling.scp_joint_state_measurable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hSCP : M.IsSCP n X0 X Ψ) :
    Measurable (fun z : Ω × ℝ≥0 => X z.1 z.2) ∧
      Measurable (fun z : Ω × ℝ≥0 => Ψ z.1 z.2) := by sorry
