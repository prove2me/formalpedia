-- Prove2me | Theorems.Thm_MaxPressure_FluidStab_maximum_pressure_fluid_model_stable
-- name    : MaxPressure.FluidStab.maximum_pressure_fluid_model_stable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:55:13.109529+00:00
-- url     : https://prove2.me/theorems/9819ec35-783c-4424-9eee-da5566c9d311
-- title:
--   Theorem 5, p. 203 — under Assumptions 1 and 2 the maximum pressure fluid model is stable if the LP has a feasible solution with ρ < 1
-- statement:
--   **Theorem 5 (Dai–Lin).** Consider a stochastic processing network satisfying the standing assumptions of §2, Assumption 1 (EAA) and Assumption 2 (there is $x\ge0$ with $Rx>0$), operating under a preemptive processor-splitting maximum pressure policy. If the static planning LP (9)–(13) has a feasible solution $(x,\rho)$ with
--   $$\rho<1,$$
--   then the corresponding fluid model is stable: there is a constant $\delta>0$ such that every fluid model solution $(\bar Z,\bar T)$ with $|\bar Z(0)|\le1$ satisfies $\bar Z(t)=0$ for all $t\ge\delta$.
--
--   Here the fluid model of a maximum pressure policy consists of the fluid model equations (14)–(18) together with the maximum pressure equation (20): at every regular time $t$, $R\dot{\bar T}(t)\cdot\bar Z(t)=\max_{a\in\mathcal E}Ra\cdot\bar Z(t)$.
--
--   Theorem 4 of the paper shows weak stability (an empty fluid model stays empty) when $\rho\le1$; Theorem 5 strengthens this, under the strict inequality $\rho<1$ and Assumption 2, to emptying in a time that is uniform over bounded initial states. Fluid stability of this kind is the standard route to positive Harris recurrence of the stochastic network under further conditions on the primitives.
--
--   **Formalization Note** The theorem's text cites "the LP (9)–(12)"; the proof needs $x\ge0$, constraint (13), so the LP is (9)–(13), as in Theorems 1, 2 and 4. Definition 4's norm $|\cdot|$ is unspecified on the page; the Euclidean norm is used, as in the proof, and any norm gives an equivalent notion. The fluid model is encoded as the predicate "(14)–(18) and (20)" on pairs of paths; its solutions are not required to arise as fluid limits. Two standing assumptions are added and disclosed: every input processor has an activity, and $m_j>0$.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 203, Theorem 5 (with Assumption 2 and Definition 4); proof p. 215, App. B

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network

namespace MaxPressure.FluidStab

open Matrix

/-- **Theorem 5**, p. 203: for a stochastic processing network satisfying Assumptions 1 and 2
and operating under a preemptive processor-splitting maximum pressure policy, the corresponding
fluid model ((14)–(18) together with (20)) is stable (Definition 4) if the LP (9)–(13) has a
feasible solution with `ρ < 1`. -/
theorem maximum_pressure_fluid_model_stable {I J K : ℕ} (N : Network I J K)
    (hN : N.Standing) (hEAA : EAA N) (h2 : Assumption2 N)
    (hLP : ∃ (x : Fin J → ℝ) (ρ : ℝ), ρ < 1 ∧ LPFeasible N x ρ) :
    FluidStable (fun (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) =>
      IsFluidSolution N Zb Tb ∧ MPFluidEq N Zb Tb) := by sorry

end MaxPressure.FluidStab
