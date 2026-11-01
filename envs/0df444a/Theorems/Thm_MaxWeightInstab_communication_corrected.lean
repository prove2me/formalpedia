-- Prove2me | Theorems.Thm_MaxWeightInstab_communication_corrected
-- name    : MaxWeightInstab.communication_corrected
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:34.503995+00:00
-- url     : https://prove2.me/theorems/92be147d-efe5-4f18-b2b4-a54fb240341b
-- title:
--   Proof of Theorem 1 (p.7), closing step (corrected: not all states communicate; every state leads to $0$ and $0$ leads to $\mathcal I_M$)
-- statement:
--   Assume (4) and (5), and fix any MaxWeight tie rule. Then:
--
--   1. from every state the chain reaches the empty state $0$ with positive probability: for every $x$ there is $n$ with $P^n(x,0)>0$;
--   2. from the empty state the chain reaches the set $\mathcal I_M$ of (13) for arbitrarily large $M$: for every $\varepsilon>0$ and every $M_0$ there are $M\ge M_0$, a state $x\in\mathcal I_M$ and $n$ with $P^n(0,x)>0$.
--
--   The paper concludes the proof of Theorem 1 with "Since all states communicate, this implies the process $Q(t)$ is transient". Not all states communicate; the two facts above are what the conclusion needs: together with the iteration bound, the empty state is transient, every state reachable from it communicates with it, and every other state leads to it without return.
--
--   Differences from the source:
--   - correction: "Since all states communicate" → every state leads to the empty state, and the empty state leads to ℐ_M for arbitrarily large M; reason: for every J ≥ 1 and ν ≥ 2 (e.g. a = 7/12, ν = 6, J = 30, which satisfy (4) and (5)) the state with Q_𝒜₁ = 2 and every other queue empty has no predecessor under any MaxWeight schedule and any arrivals: no service at 𝒜ⱼ (j ≥ 1) since ℬ₀ is empty, Q_𝒜₀ ≤ 1, Q_𝒜₁ ≥ 1, and then putting ν units on 𝒜₁ has weight ≥ ν ≥ 2 > 1 (proved in Lean, Solutions/verification/MaxWeightInstab_sanity.lean, no_predecessor)
--   - encoding: ties in (1) broken "arbitrarily (or randomly)" (p.1) → every tie rule π : State → PMF State supported on the maximizers of (1); reason: deterministic rules are the point-mass case; covers both
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, proof of Theorem 1, p.7

import Mathlib
import Definitions.Def_MatrixAnalytic_Stability_Chain
import Definitions.Def_MaxWeightInstab_IsInitial
import Definitions.Def_MaxWeightInstab_transMat
import Definitions.Def_MaxWeightInstab_IsTieRule
import Definitions.Def_MaxWeightInstab_rRho

namespace MaxWeightInstab

/-- **Communication step of the proof of Theorem 1, corrected** (Bramson, D'Auria & Walton, arXiv:1909.10825v2, p.7). The paper closes the
proof with "Since all states communicate, this implies the process Q(t) is transient". Not all
states communicate (the state with two jobs at `𝒜₁` and no other job has no predecessor when
`ν ≥ 2`). What the conclusion needs holds: (i) from every state the chain reaches the empty state
with positive probability, and (ii) from the empty state it reaches a state of `ℐ_M` for
arbitrarily large `M`, for every `ε > 0`.

**Formalization Note.** `stepPow P n x y` is the `n`-step transition probability. Stated for every
MaxWeight tie rule and every `J, ν, a` satisfying (4) and (5). -/
theorem communication_corrected (J ν : ℕ) (a : ℝ) (h4 : rRho a ν < 1)
    (h5ν : 1 < ν ∧ ν < J)
    (h5a : (J : ℝ) / (2 * J - ν) < a ∧
      a < 1 - ((J : ℝ) + ν) * ((J : ℝ) + (ν : ℝ) ^ 2) / ((ν : ℝ) * ((J : ℝ) ^ 2 + J + (ν : ℝ) ^ 2)))
    (π : State J → PMF (State J)) (hπ : IsTieRule ν π) :
    (∀ x : State J, ∃ n : ℕ, 0 < MatrixAnalytic.Stability.stepPow (transMat a π) n x 0) ∧
    (∀ ε : ℝ, 0 < ε → ∀ M₀ : ℝ, ∃ M : ℝ, M₀ ≤ M ∧ ∃ x : State J, IsInitial ν ε M x ∧
      ∃ n : ℕ, 0 < MatrixAnalytic.Stability.stepPow (transMat a π) n 0 x) := by sorry

end MaxWeightInstab
