-- Prove2me | Theorems.Thm_MaxPressure_FluidStab_Supplement_stability_requires_static_allocation
-- name    : MaxPressure.FluidStab.Supplement.stability_requires_static_allocation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:13:44.022297+00:00
-- url     : https://prove2.me/theorems/f2a3129e-0c1b-4545-a717-0a4bacbec3d9
-- title:
--   Theorem 7 (corrected: finite rates) — stability requires SAP feasibility
-- statement:
--   Under the structural assumptions and primitive strong laws (3)–(4), suppose some non-processor-splitting general service policy is pathwise stable for every legal initial state. Then the static allocation problem is feasible:
--
--   $$\exists\pi\ge0:\quad\sum_{a\in\mathcal N}\pi_a=1,\qquad R\left(\sum_{a\in\mathcal N}a\pi_a\right)=0.$$
--
--   The set $\mathcal N$ contains all integer allocations, including feasible service idling. Preemption is allowed and no EAA assumption is made. This conclusion asserts a probability mixture of integer allocations; mere feasibility of the weaker static planning LP is not substituted for SAP. The occupation frequencies must be obtained in a proof, not assumed in the policy.
--
--   Differences from the source:
--   - correction: The page permits nonnegative mean requirements and presupposes input processors can work. → The published Standing predicate requires positive means and an activity at each input processor.; reason: These are the inherited disclosed finite-rate and nonidling conventions; zero mean rates and unused input processors are excluded.
--   - encoding: General physical service histories and arbitrary initial states are described in prose. → Explicit episodes, immutable job ownership, finite residual initialization and all-state almost-sure stability.; reason: This makes the source service assumptions binding; actual finishes handle zero-duration opportunities and time-zero cleanup.
--   - generalization: History-dependent randomized service policies are based on past states and completion decisions. → Arbitrary realized choices, including anticipating choices and additional locally finite decision times, satisfy the physical rules.; reason: The assertions are pathwise and remain valid for this larger policy class; all source policies are included.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 206, Theorem 7; https://doi.org/10.1287/opre.1040.0170

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Supplement_Histories

namespace MaxPressure.FluidStab.Supplement

open MeasureTheory Filter Topology

theorem stability_requires_static_allocation
    {I J K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (N : FluidStab.Network I J K) (P : Throughput.Primitives I J Ω)
    (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (hN : N.Standing) (hP : P.Valid (throughputNetwork N) Pr)
    (hstable : ∃ p : Policy I J Ω,
      Admissible N P Pr p false ∧ IntegerPolicy N Pr p false ∧ Stable N Pr p false) :
    SAPFeasible N := by sorry

end MaxPressure.FluidStab.Supplement
