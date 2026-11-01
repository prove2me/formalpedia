-- Prove2me | Theorems.Thm_MaxWeightInstab_theorem_1
-- name    : MaxWeightInstab.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:32.405576+00:00
-- url     : https://prove2.me/theorems/f4208e80-f462-43a0-b329-df9619997ae3
-- title:
--   Theorem 1 — MaxWeight is transient in a subcritical multihop switched network
-- statement:
--   Consider the MaxWeight policy for the single class multihop switched network of Figure 1: two components $\mathcal A=\{\mathcal A_0,\dots,\mathcal A_J\}$ and $\mathcal B=\{\mathcal B_0,\dots,\mathcal B_J\}$; each of the $2J$ queues $\mathcal A_j,\mathcal B_j$ ($j\ge1$) receives in each time unit one external arrival with probability $a/J$, independently; jobs served at $\mathcal A_j$ move to $\mathcal B_0$, jobs served at $\mathcal B_j$ move to $\mathcal A_0$, and jobs served at $\mathcal A_0,\mathcal B_0$ leave; the feasible schedules $\mathcal S$ are given by (3), and in each time unit a schedule maximizing $\sum_jQ_j\sigma_j$ over $\mathcal S$ is used, ties broken arbitrarily or randomly. Assume
--
--   $$
--   r_{\boldsymbol\rho}=a\left(1+\frac1\nu\right)<1 \tag{4}
--   $$
--
--   and
--
--   $$
--   1<\nu<J\qquad\text{and}\qquad \frac{J}{2J-\nu}<a<1-\frac{(J+\nu)(J+\nu^2)}{\nu(J^2+J+\nu^2)} . \tag{5}
--   $$
--
--   Then $\boldsymbol\rho\in\mathcal C$ and the associated queueing network process $\mathcal Q$ is transient: from every state, the probability of never returning to it is positive.
--
--   The parameters $a=7/12$, $\nu=6$, $J=30$ satisfy (4) and (5). The theorem shows that MaxWeight is not maximally stable for single class multihop switched networks.
--
--   **Formalization Note** The queueing network process is the Markov chain on $\mathbb Z_+^{2J+2}$ that, in each time unit, serves $\sigma_j\wedge Q_j$ jobs at each queue with $\sigma$ drawn from the tie rule at the current state, routes the served jobs, and then adds the arrivals. The statement holds for every tie rule.
--
--   Differences from the source:
--   - reading: arrivals "at rate a, that choose randomly between the corresponding J queues", at most one per queue per time unit (p.3), independent across queues (p.5) → independent Bernoulli(a/J) arrivals at each of the 2J external queues, i.i.d. over time units; reason: the p.5 independence rules out one multinomial arrival per end
--   - encoding: ties in (1) broken "arbitrarily (or randomly)" (p.1) → every tie rule π : State → PMF State supported on the maximizers of (1); reason: deterministic rules are the point-mass case; covers both
--   - encoding: (3) with the factor 1/ν → ν σ_𝒜₀ + Σ_{j≥1} σ_𝒜ⱼ ≤ ν over ℕ (and the same for ℬ); reason: (3) multiplied by ν ≥ 1; same set
--   - encoding: "𝐐 is transient" → IsTransientChain: no state is recurrent (every state has positive probability of never returning); reason: the standard meaning for a chain that is not irreducible; for an irreducible chain it is equivalent to the transience of one state
--   - encoding: 𝒞 = interior of the convex closure < 𝒮 > → interior of the convex hull of 𝒮 ⊂ ℝ^{2J+2}; reason: 𝒮 is finite, so its convex hull is closed
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, Theorem 1, p.3

import Mathlib
import Definitions.Def_MatrixAnalytic_Stability_Chain
import Definitions.Def_MaxWeightInstab_rho
import Definitions.Def_MaxWeightInstab_subcriticalRegion
import Definitions.Def_MaxWeightInstab_rRho
import Definitions.Def_MaxWeightInstab_transMat
import Definitions.Def_MaxWeightInstab_IsTieRule

namespace MaxWeightInstab

/-- **Theorem 1** (Bramson, D'Auria & Walton, arXiv:1909.10825v2, p.3). Consider the MaxWeight policy for the single class multihop
switched network represented by Figure 1 and with `𝒮` given by (3). Assume that (4) is satisfied
and that `1 < ν < J` and `J/(2J − ν) < a < 1 − (J + ν)(J + ν²)/(ν(J² + J + ν²))` (5). Then `ρ ∈ 𝒞`
and the associated queueing network process `𝐐` is transient.

**Formalization Note.** The queueing network process is the Markov chain `transMat a π` on
`ℤ₊^{2J+2}`: serve `min(σ_j, Q_j)` with `σ` a MaxWeight schedule for the current queue lengths,
route `𝒜_j → ℬ₀`, `ℬ_j → 𝒜₀` (`j ≥ 1`), `𝒜₀, ℬ₀ →` out, then add independent Bernoulli(`a/J`)
arrivals at the `2J` external queues. The statement holds for every tie rule `π` (arbitrary or
random choice among maximizers). "Transient" is `IsTransientChain`: no state is recurrent, i.e.
from every state the probability of never returning is positive (the chain is not irreducible). -/
theorem theorem_1 (J ν : ℕ) (a : ℝ) (h4 : rRho a ν < 1)
    (h5ν : 1 < ν ∧ ν < J)
    (h5a : (J : ℝ) / (2 * J - ν) < a ∧
      a < 1 - ((J : ℝ) + ν) * ((J : ℝ) + (ν : ℝ) ^ 2) / ((ν : ℝ) * ((J : ℝ) ^ 2 + J + (ν : ℝ) ^ 2)))
    (π : State J → PMF (State J)) (hπ : IsTieRule ν π) :
    rho a J ∈ subcriticalRegion J ν ∧
      MatrixAnalytic.Stability.IsTransientChain (transMat a π) := by sorry

end MaxWeightInstab
