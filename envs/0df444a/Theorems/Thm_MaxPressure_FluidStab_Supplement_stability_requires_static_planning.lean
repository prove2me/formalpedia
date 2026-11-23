-- Prove2me | Theorems.Thm_MaxPressure_FluidStab_Supplement_stability_requires_static_planning
-- name    : MaxPressure.FluidStab.Supplement.stability_requires_static_planning
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:11:19.112584+00:00
-- url     : https://prove2.me/theorems/b6350a0b-74df-4e01-a2e4-f5c99f2711b6
-- title:
--   Theorem 1 (corrected: finite rates) — stability requires LP feasibility
-- statement:
--   Let a finite stochastic processing network satisfy the structural assumptions of §2 and the primitive strong laws (3)–(4). If some general service policy is pathwise stable for every legal initial state, then the static planning LP has a feasible point with load at most one:
--
--   $$\exists x\ge0,\ \exists\rho\le1:\quad Rx=0,\quad \sum_j A_{kj}x_j\le\rho\ (k\text{ service}),\quad \sum_j A_{kj}x_j=1\ (k\text{ input}).$$
--
--   This is a necessary condition under arbitrary general policies, including fractional allocations, preemption and randomized history dependence. It assumes neither EAA nor maximum pressure. No limiting occupation distribution is supplied as a premise.
--
--   Differences from the source:
--   - correction: The page permits nonnegative mean requirements and presupposes input processors can work. → The published Standing predicate requires positive means and an activity at each input processor.; reason: These are the inherited disclosed finite-rate and nonidling conventions; zero mean rates and unused input processors are excluded.
--   - encoding: General physical service histories and arbitrary initial states are described in prose. → Explicit episodes, immutable job ownership, finite residual initialization and all-state almost-sure stability.; reason: This makes the source service assumptions binding; actual finishes handle zero-duration opportunities and time-zero cleanup.
--   - generalization: History-dependent randomized service policies are based on past states and completion decisions. → Arbitrary realized choices, including anticipating choices and additional locally finite decision times, satisfy the physical rules.; reason: The assertions are pathwise and remain valid for this larger policy class; all source policies are included.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 202, Theorem 1; https://doi.org/10.1287/opre.1040.0170

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Supplement_Histories

namespace MaxPressure.FluidStab.Supplement

open MeasureTheory Filter Topology

theorem stability_requires_static_planning
    {I J K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (N : FluidStab.Network I J K) (P : Throughput.Primitives I J Ω)
    (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (hN : N.Standing) (hP : P.Valid (throughputNetwork N) Pr)
    (hstable : ∃ p : Policy I J Ω,
      Admissible N P Pr p false ∧ Stable N Pr p false) :
    ∃ x : Fin J → ℝ, ∃ ρ : ℝ, ρ ≤ 1 ∧ LPFeasible N x ρ := by sorry

end MaxPressure.FluidStab.Supplement
