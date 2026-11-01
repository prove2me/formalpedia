-- Prove2me | Theorems.Thm_MaxWeightInstab_theorem_1_iteration
-- name    : MaxWeightInstab.theorem_1_iteration
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:27.458145+00:00
-- url     : https://prove2.me/theorems/9baac984-b49a-4477-a532-ff7f0efa56d9
-- title:
--   Proof of Theorem 1 (p.7) — from $\mathcal I_M$ the total queue length stays above $\tfrac12\tfrac{a}{a+\nu}M$ except with probability $\le\sum_k e^{-\eta\gamma^kT}$
-- statement:
--   Assume (4) and (5) and let $\gamma$ satisfy (11). There are $\varepsilon_0,L>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$ there are $\eta>0$ and $M_0$ with the following property. For every $M\ge\max(L/\varepsilon,M_0)$, every MaxWeight tie rule and every initial state $Q_0\in\mathcal I_M$,
--
--   $$
--   \mathbb P_{Q_0}\Big(Q^\Sigma_{\mathcal A}(t)+Q^\Sigma_{\mathcal B}(t)<\frac12\,\frac{a}{a+\nu}\,M\ \text{ for some } t\ge0\Big)\ \le\ \sum_{k=0}^\infty e^{-\eta\gamma^kT} .
--   $$
--
--   The paper obtains it by iterating (16) and Proposition 1 with the strong Markov property and the $\mathcal A\leftrightarrow\mathcal B$ symmetry of the network. Since the right-hand side is less than $1$ for large $M$, the network started in $\mathcal I_M$ never empties with positive probability.
--
--   **Formalization Note** The probability of entering the set $\{y:Q^\Sigma_{\mathcal A}(y)+Q^\Sigma_{\mathcal B}(y)<\tfrac12\tfrac{a}{a+\nu}M\}$ at some time is the increasing limit over $n$ of one minus the probability of avoiding it at times $1,\dots,n$, so the bound is stated for every $n$ (the initial state is not in the set).
--
--   Differences from the source:
--   - encoding: ℙ_{Q₀}(… for some t ≥ 0) → for every n, 1 − ℙ_x(avoid the set at times 1, …, n) (setAvoidTailC); reason: the hitting probability is the increasing limit of these; the initial state is outside the set
--   - reading: ε₀, L depend on a, J, ν, γ; ε ∈ (0, ε₀), M ≥ L/ε (pp.6–7); η the "new choice" of (16); M large enough that T ≥ C → ∃ ε₀, L > 0, ∀ ε ∈ (0, ε₀), ∃ η > 0, ∃ M₀, ∀ M ≥ max(L/ε, M₀); reason: the quantifier order of pp.6–7; η comes from (16) after ε is fixed
--   - encoding: ties in (1) broken "arbitrarily (or randomly)" (p.1) → every tie rule π : State → PMF State supported on the maximizers of (1); reason: deterministic rules are the point-mass case; covers both
--   - reading: arrivals "at rate a, that choose randomly between the corresponding J queues", at most one per queue per time unit (p.3), independent across queues (p.5) → independent Bernoulli(a/J) arrivals at each of the 2J external queues, i.i.d. over time units; reason: the p.5 independence rules out one multinomial arrival per end
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, proof of Theorem 1, p.7

import Mathlib
import Definitions.Def_MatrixAnalytic_Stability_Chain
import Definitions.Def_MaxWeightInstab_IsInitial
import Definitions.Def_MaxWeightInstab_horizon
import Definitions.Def_MaxWeightInstab_transMat
import Definitions.Def_MaxWeightInstab_IsTieRule
import Definitions.Def_MaxWeightInstab_totalA
import Definitions.Def_MaxWeightInstab_totalB

namespace MaxWeightInstab

/-- **Iteration display in the proof of Theorem 1** (Bramson, D'Auria & Walton, arXiv:1909.10825v2, p.7). "Iteration using the Strong
Markov property implies that
`ℙ_{Q₀}(Q^Σ_𝒜(t) + Q^Σ_ℬ(t) < (1/2)(a/(a + ν)) M for some t ≥ 0) ≤ ∑_{k=0}^∞ e^{−ηγ^k T}`"
for every initial state `Q₀ ∈ ℐ_M`, the queueing network process being the MaxWeight chain of
Figure 1 with any tie rule.

**Formalization Note.** The probability that the chain started at `x` enters
`A = {y : Q^Σ_𝒜(y) + Q^Σ_ℬ(y) < (1/2)(a/(a+ν))M}` at some time `t ≥ 0` is the increasing limit over `n`
of `1 − P_x[avoid A at times 1, …, n]` (`setAvoidTailC`; `x ∉ A` since `Q^Σ_ℬ(x) = M`), so the bound is
stated for every `n`. Quantifiers as on pp.6–7: `ε₀, L` depend on `a, J, ν, γ`; `η` on `ε` (it comes
from (16)); `M₀` on `ε`. Hypotheses (4), (5), (11) are the standing assumptions of §3.1. -/
theorem theorem_1_iteration (J ν : ℕ) (a γ : ℝ) (h4 : rRho a ν < 1)
    (h5ν : 1 < ν ∧ ν < J)
    (h5a : (J : ℝ) / (2 * J - ν) < a ∧
      a < 1 - ((J : ℝ) + ν) * ((J : ℝ) + (ν : ℝ) ^ 2) / ((ν : ℝ) * ((J : ℝ) ^ 2 + J + (ν : ℝ) ^ 2)))
    (h11 : 1 < γ ∧ γ < a / (1 - a + a * ν / J)) :
    ∃ ε₀ > 0, ∃ L > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ η > 0, ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M →
      L / ε ≤ M → ∀ π : State J → PMF (State J), IsTieRule ν π →
        ∀ x : State J, IsInitial ν ε M x → ∀ n : ℕ,
          1 - MatrixAnalytic.Stability.setAvoidTailC (transMat a π) x
              {y | ((totalA y : ℝ) + totalB y) < 1 / 2 * (a / (a + ν)) * M} n ≤
            ∑' k : ℕ, Real.exp (-η * γ ^ k * horizon a ν M) := by sorry

end MaxWeightInstab
