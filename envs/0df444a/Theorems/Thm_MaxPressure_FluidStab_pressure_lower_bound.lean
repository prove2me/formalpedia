-- Prove2me | Theorems.Thm_MaxPressure_FluidStab_pressure_lower_bound
-- name    : MaxPressure.FluidStab.pressure_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:54:45.761194+00:00
-- url     : https://prove2.me/theorems/d87d4ba5-31dd-467c-a7b8-df53a52c2948
-- title:
--   Proof of Theorem 5, p. 215 — RṪ(t)·Z̄(t) ≥ Rx*·Z̄(t) ≥ δ Σ_i Z̄_i(t) ≥ δ‖Z̄(t)‖ at regular times
-- statement:
--   Let a stochastic processing network satisfy the standing assumptions of §2, and let $(\bar Z,\bar T)$ be a maximum pressure fluid model solution: it satisfies (14)–(18) and (20). Let $x^*\in\mathcal A$ and $\delta>0$ satisfy $Rx^*\ge\delta e$. Then at every regular time $t$
--   $$R\dot{\bar T}(t)\cdot\bar Z(t)\ \ge\ Rx^*\cdot\bar Z(t)\ \ge\ \delta\sum_i\bar Z_i(t)\ \ge\ \delta\|\bar Z(t)\|,$$
--   where $\|\cdot\|$ is the Euclidean norm on $\mathbb R^I$.
--
--   The first inequality is where the maximum pressure policy enters: by (20) the instantaneous allocation $\dot{\bar T}(t)$ attains the largest pressure over $\mathcal E$, hence over $\mathcal A$.
--
--   **Formalization Note** The three inequalities are stated as three conjuncts. Assumptions 1 and 2 and the LP are not hypotheses here: only the properties of $x^*$ and $\delta$ they produce are used.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 215, proof of Theorem 5 (App. B), first display

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network

namespace MaxPressure.FluidStab

open Matrix

/-- Proof of Theorem 5, App. B, p. 215: let `(Z̄, T̄)` be a maximum pressure fluid model
solution ((14)–(18) and (20)), `x* ∈ 𝒜` and `ε > 0` with `Rx* ≥ εe`. At every regular time `t`,
`R Ṫ(t) · Z̄(t) ≥ Rx* · Z̄(t) ≥ ε ∑_i Z̄_i(t) ≥ ε ‖Z̄(t)‖`, with `‖·‖` the Euclidean norm. -/
theorem pressure_lower_bound {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (hsol : IsFluidSolution N Zb Tb) (hmp : MPFluidEq N Zb Tb)
    (xs : Fin J → ℝ) (hxs : xs ∈ allocSet N) (ε : ℝ) (hε : 0 < ε)
    (hR : ∀ i, ε ≤ (R N *ᵥ xs) i) (t : ℝ) (ht : IsRegular Zb Tb t) :
    pressure N xs (Zb t) ≤ pressure N (deriv Tb t) (Zb t) ∧
    ε * ∑ i, Zb t i ≤ pressure N xs (Zb t) ∧
    ε * Real.sqrt (∑ i, Zb t i ^ 2) ≤ ε * ∑ i, Zb t i := by sorry

end MaxPressure.FluidStab
