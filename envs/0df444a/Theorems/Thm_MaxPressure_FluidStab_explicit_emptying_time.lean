-- Prove2me | Theorems.Thm_MaxPressure_FluidStab_explicit_emptying_time
-- name    : MaxPressure.FluidStab.explicit_emptying_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:55:08.282386+00:00
-- url     : https://prove2.me/theorems/5b152d6b-5689-4075-a57d-cfadb6e3cb70
-- title:
--   Proof of Theorem 5, p. 215 — Z̄(t) = 0 for t ≥ ‖Z̄(0)‖/δ
-- statement:
--   Let a stochastic processing network satisfy the standing assumptions of §2, Assumption 1 (EAA) and Assumption 2, and suppose the static planning LP (9)–(13) has a feasible solution with $\rho<1$. Then there is a constant $\delta>0$ such that every maximum pressure fluid model solution $(\bar Z,\bar T)$ (satisfying (14)–(18) and (20)) has
--   $$\bar Z(t)=0\qquad\text{for all } t\ge\|\bar Z(0)\|/\delta,$$
--   where $\|\cdot\|$ is the Euclidean norm.
--
--   This is the last line of the proof of Theorem 5 and gives an explicit emptying time, linear in the initial fluid level. Theorem 5 follows with the constant of Definition 4 equal to $1/\delta$.
--
--   **Formalization Note** $\delta$ depends only on the network (it is $\min_i(R\hat x)_i$ for the vector of the proof), not on the solution. Assumption 1 is a hypothesis because the paper states the result under it (it justifies (20)); the fluid-level argument does not use it.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 215, proof of Theorem 5 (App. B), last sentence

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network

namespace MaxPressure.FluidStab

open Matrix

/-- Proof of Theorem 5, App. B, p. 215 (last line): under Assumptions 1 and 2, if the LP (9)–(13)
has a feasible solution with `ρ < 1`, there is `ε > 0` (the paper's `δ`) such that every maximum
pressure fluid model solution has `Z̄(t) = 0` for `t ≥ ‖Z̄(0)‖/ε`. -/
theorem explicit_emptying_time {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hEAA : EAA N) (h2 : Assumption2 N)
    (hLP : ∃ (x : Fin J → ℝ) (ρ : ℝ), ρ < 1 ∧ LPFeasible N x ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ),
      IsFluidSolution N Zb Tb → MPFluidEq N Zb Tb →
      ∀ t, Real.sqrt (∑ i, Zb 0 i ^ 2) / ε ≤ t → Zb t = 0 := by sorry

end MaxPressure.FluidStab
