-- Prove2me | Theorems.Thm_MaxPressure_FluidStab_Supplement_nonpreemptive_reversed_leontief_stable
-- name    : MaxPressure.FluidStab.Supplement.nonpreemptive_reversed_leontief_stable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:22:20.241615+00:00
-- url     : https://prove2.me/theorems/3d9ea7d9-c827-46e5-8570-9d425722ecf4
-- title:
--   Theorem 9 (corrected: finite rates) — nonpreemptive reversed Leontief stability
-- statement:
--   Consider a reversed Leontief stochastic processing network satisfying EAA (Assumption 1), the structural and primitive assumptions (3)–(4), and Assumption 3 with activity-dependent real exponents. If the static planning LP has a feasible $(x,\rho)$ with $\rho\le1$, every admissible nonpreemptive, non-processor-splitting maximum-pressure policy is pathwise stable:
--
--   $$\forall s\text{ legal},\quad\Pr\!\left(\forall i,\ \lim_{t\to\infty}Z_i^s(t)/t=0\right)=1.$$
--
--   The policy maximizes over the same physical feasible extremes as Lemma 2 while retaining the jobs and processors of all unfinished activities. Initial queue lengths and compatible residual commitments are arbitrary. No residual blocking estimate, fluid maximum-pressure identity or stability assumption is hidden in the policy predicate. Equality $\rho=1$ is retained.
--
--   Differences from the source:
--   - correction: The page permits nonnegative mean requirements and presupposes input processors can work. → The published Standing predicate requires positive means and an activity at each input processor.; reason: These are the inherited disclosed finite-rate and nonidling conventions; zero mean rates and unused input processors are excluded.
--   - encoding: General physical service histories and arbitrary initial states are described in prose. → Explicit episodes, immutable job ownership, finite residual initialization and all-state almost-sure stability.; reason: This makes the source service assumptions binding; actual finishes handle zero-duration opportunities and time-zero cleanup.
--   - generalization: History-dependent randomized service policies are based on past states and completion decisions. → Arbitrary realized choices, including anticipating choices and additional locally finite decision times, satisfy the physical rules.; reason: The assertions are pathwise and remain valid for this larger policy class; all source policies are included.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 208, Theorem 9; https://doi.org/10.1287/opre.1040.0170

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Supplement_Residuals

namespace MaxPressure.FluidStab.Supplement

open MeasureTheory Filter Topology

theorem nonpreemptive_reversed_leontief_stable
    {I J K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (N : FluidStab.Network I J K) (P : Throughput.Primitives I J Ω)
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (p : Policy I J Ω)
    (hN : N.Standing) (hP : P.Valid (throughputNetwork N) Pr)
    (hrev : ReversedLeontief.IsReversedLeontief (reversedNetwork N))
    (hEAA : EAA N) (hmoment : Assumption3 P Pr)
    (hLP : ∃ x : Fin J → ℝ, ∃ ρ : ℝ, ρ ≤ 1 ∧ LPFeasible N x ρ)
    (hlegal : Admissible N P Pr p true)
    (hMP : MaximumPressurePolicy N Pr p (extremeAllocs N) true) :
    Stable N Pr p true := by sorry

end MaxPressure.FluidStab.Supplement
