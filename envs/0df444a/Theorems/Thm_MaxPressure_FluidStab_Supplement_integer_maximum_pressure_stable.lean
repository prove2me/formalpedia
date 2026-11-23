-- Prove2me | Theorems.Thm_MaxPressure_FluidStab_Supplement_integer_maximum_pressure_stable
-- name    : MaxPressure.FluidStab.Supplement.integer_maximum_pressure_stable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:16:30.799801+00:00
-- url     : https://prove2.me/theorems/e1c21f23-ab4f-449d-a3fd-5d2ba0624c6d
-- title:
--   Theorem 8 (corrected: finite rates) — integer maximum pressure is stable
-- statement:
--   Let a general finite stochastic processing network satisfy the structural assumptions, primitive strong laws (3)–(4), and EAA with $\mathcal N$ in place of $\mathcal E$. If SAP (24)–(27) is feasible, every admissible non-processor-splitting maximum-pressure policy is pathwise stable:
--
--   $$\forall s\text{ legal},\quad \Pr\!\left(\forall i,\ \lim_{t\to\infty}Z_i^s(t)/t=0\right)=1.$$
--
--   The maximization is over physically feasible integer allocations and permits preemption. The network need not be reversed Leontief, and $\mathcal N=\mathcal E$ is not a premise. Neither strict LP slack nor Assumptions 2 and 3 are required. This is the sufficiency counterpart to Theorem 7.
--
--   Differences from the source:
--   - correction: The page permits nonnegative mean requirements and presupposes input processors can work. → The published Standing predicate requires positive means and an activity at each input processor.; reason: These are the inherited disclosed finite-rate and nonidling conventions; zero mean rates and unused input processors are excluded.
--   - encoding: General physical service histories and arbitrary initial states are described in prose. → Explicit episodes, immutable job ownership, finite residual initialization and all-state almost-sure stability.; reason: This makes the source service assumptions binding; actual finishes handle zero-duration opportunities and time-zero cleanup.
--   - generalization: History-dependent randomized service policies are based on past states and completion decisions. → Arbitrary realized choices, including anticipating choices and additional locally finite decision times, satisfy the physical rules.; reason: The assertions are pathwise and remain valid for this larger policy class; all source policies are included.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 206, Theorem 8; https://doi.org/10.1287/opre.1040.0170

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Supplement_Histories

namespace MaxPressure.FluidStab.Supplement

open MeasureTheory Filter Topology

theorem integer_maximum_pressure_stable
    {I J K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (N : FluidStab.Network I J K) (P : Throughput.Primitives I J Ω)
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (p : Policy I J Ω)
    (hN : N.Standing) (hP : P.Valid (throughputNetwork N) Pr)
    (hEAA : IntegerEAA N) (hSAP : SAPFeasible N)
    (hlegal : Admissible N P Pr p false)
    (hMP : MaximumPressurePolicy N Pr p (integerAllocs N) false) :
    Stable N Pr p false := by sorry

end MaxPressure.FluidStab.Supplement
