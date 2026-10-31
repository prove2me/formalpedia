-- Prove2me | Theorems.Thm_LinearZeroSumMG_lemma_4
-- name    : LinearZeroSumMG.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:54:03.668892+00:00
-- url     : https://prove2.me/theorems/d57458d1-9b39-40c4-8350-7b1481083714
-- title:
--   Lemma 4, p.20 — $\sigma^k_h(x)$ is a $2\varepsilon$-CCE of $(\overline Q^k_h(x,\cdot,\cdot),\underline Q^k_h(x,\cdot,\cdot))$
-- statement:
--   **Lemma 4 (Algorithm 2 finds a $2\varepsilon$-CCE).** Consider Algorithm 1 with a CCE rule (every output is a CCE of its input pair), any rounding rule and any data sequence. Fix $(k,h,x)$ and $\varepsilon\ge0$, and suppose the pair $(\widetilde Q,\underset{\sim}{Q})$ picked by FIND_CCE at $(k,h)$ is $\varepsilon$-close to $(\overline Q^k_h,\underline Q^k_h)$ at the state $x$: $|\widetilde Q(x,a,b)-\overline Q^k_h(x,a,b)|\le\varepsilon$ and $|\underset{\sim}{Q}(x,a,b)-\underline Q^k_h(x,a,b)|\le\varepsilon$ for all $(a,b)$. Then $\sigma=\sigma^k_h(x)$ is a $2\varepsilon$-CCE of the matrix game with payoff $\overline Q^k_h(x,\cdot,\cdot)$ for P1 and $\underline Q^k_h(x,\cdot,\cdot)$ for P2:
--   $$
--   \mathbb E_{(a,b)\sim\sigma}\big[\overline Q^k_h(x,a,b)\big]\ge\mathbb E_{b\sim\mathcal P_2\sigma}\big[\overline Q^k_h(x,a',b)\big]-2\varepsilon\quad\forall a',\qquad
--   \mathbb E_{(a,b)\sim\sigma}\big[\underline Q^k_h(x,a,b)\big]\le\mathbb E_{a\sim\mathcal P_1\sigma}\big[\underline Q^k_h(x,a,b')\big]+2\varepsilon\quad\forall b'.
--   $$
--
--   Although CCE values are not Lipschitz in the payoffs, CCE policies are stable under rounding; this is why rounding inside the algorithm (rather than only in the analysis) works.
--
--   Differences from the source:
--   - reading: second inequality 𝔼_{σ̃}[Q̲^k_h(x, a, b)] ≤ 𝔼_{a∼𝒫₁σ̃}[Q̄^k_h(x, a, b′)] + 2ε (Q̄ on the right) → Q̲^k_h on both sides; reason: the lemma asserts a 2ε-CCE "in the sense that", and the CCE definition (1b) has P2's payoff Q̲ on both sides; Lemma 5's lower bounds (a), (i), proved "in a similar fashion", need Q̲
--   - generalization: the ε-closeness guaranteed by Algorithm 2's line 2 for the minimum net and ε of Theorem 1 → ε-closeness at the state x as a hypothesis, for every ε, every rounding rule and every CCE rule (measurability not needed); reason: the proof uses only the closeness at x and the CCE property of the rounded game; the algorithm's setting is a special case
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, Lemma 4, p.20; proof, p.21

import Mathlib
import Definitions.Def_LinearZeroSumMG_omni

namespace LinearZeroSumMG

/-- **Lemma 4 (Algorithm 2 Finds `2ε`-CCE).**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, Lemma 4, p.20: "For each `(k, h, x)`,
`σ^k_h(x)` is an `2ε`-CCE of `(Q̄^k_h(x, ·, ·), Q̲^k_h(x, ·, ·))` in the sense that
`𝔼_{(a,b)∼σ̃(x)}[Q̄^k_h(x, a, b)] ≥ 𝔼_{b∼𝒫₂σ̃(x)}[Q̄^k_h(x, a', b)] − 2ε, ∀a' ∈ 𝒜`,
`𝔼_{(a,b)∼σ̃(x)}[Q̲^k_h(x, a, b)] ≤ 𝔼_{a∼𝒫₁σ̃(x)}[Q̄^k_h(x, a, b')] + 2ε, ∀b' ∈ 𝒜`."

For every game, every input of Algorithm 1 whose CCE rule returns coarse correlated equilibria,
every data sequence, every `(k, h, x)` and every `ε`: if the pair `(Q̃, Q̰)` picked by `FIND_CCE` at
`(k, h)` is `ε`-close to `(Q̄^k_h, Q̲^k_h)` at the state `x`, then `σ^k_h(x)` is a `2ε`-CCE of the matrix game
with payoff `Q̄^k_h(x, ·, ·)` for P1 (maximizer) and `Q̲^k_h(x, ·, ·)` for P2 (minimizer).

**Formalization Note**
- The second printed inequality has `Q̄^k_h` on the right-hand side; it is read as `Q̲^k_h`, the payoff
  of P2 on both sides, as in the CCE definition (1b) and as Lemma 5's lower bounds use it.
- The `ε`-closeness that line 2 of Algorithm 2 guarantees is a hypothesis (it holds whenever the
  input lies in the class `𝒬`); it is needed only at the state `x`. -/
theorem lemma_4 {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A] {d : ℕ}
    (G : MarkovGame S A) (P : OmniParams S A d)
    (hcce : ∀ u₁ u₂ : A → A → ℝ, IsCCE u₁ u₂ (P.cce u₁ u₂))
    (xs : ℕ → ℕ → S) (as bs : ℕ → ℕ → A) (k h : ℕ) (x : S) (ε : ℝ)
    (hclose : ∀ a b,
      |(omni G P xs as bs k h).pick.1 x a b - (omni G P xs as bs k h).QUp x a b| ≤ ε ∧
      |(omni G P xs as bs k h).pick.2 x a b - (omni G P xs as bs k h).QLo x a b| ≤ ε) :
    IsApproxCCE (2 * ε) ((omni G P xs as bs k h).QUp x) ((omni G P xs as bs k h).QLo x)
      ((omni G P xs as bs k h).sigma x) := by sorry

end LinearZeroSumMG
