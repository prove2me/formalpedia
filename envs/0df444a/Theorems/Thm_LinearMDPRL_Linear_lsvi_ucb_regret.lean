-- Prove2me | Theorems.Thm_LinearMDPRL_Linear_lsvi_ucb_regret
-- name    : LinearMDPRL.Linear.lsvi_ucb_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:45:08.801412+00:00
-- url     : https://prove2.me/theorems/3406357c-5b6d-4fa5-b2a5-aeaaf39d00be
-- title:
--   Theorem 3.1, p. 7 — LSVI-UCB with λ = 1, β = c·dH√ι: with probability 1 − p, Regret(K) ≤ C·√(d³H³Tι²)
-- statement:
--   This is the main theorem of Jin, Yang, Wang and Jordan.
--
--   Let $\mathrm{MDP}(\mathcal S,\mathcal A,H,\mathbb P,r)$ be a linear MDP with feature map $\phi:\mathcal S\times\mathcal A\to\mathbb R^d$ (Assumption A), where $\mathcal S$ is any measurable space and $\mathcal A$ any finite set. Let $K$ be the number of episodes, $T=KH$, $p\in(0,1)$ and $\iota=\log(2dT/p)$. There exist absolute constants $c>0$ and $C>0$ such that, if LSVI-UCB (Algorithm 1) is run with
--   $$
--   \lambda=1,\qquad \beta=c\cdot dH\sqrt\iota,
--   $$
--   against any adversarial choice of initial states, then with probability at least $1-p$
--   $$
--   \mathrm{Regret}(K)=\sum_{k=1}^K\big[V^\star_1(x^k_1)-V^{\pi_k}_1(x^k_1)\big]\le C\sqrt{d^3H^3T\iota^2}.
--   $$
--
--   The bound is polynomial in $d$ and $H$ and does not depend on the number of states or actions; it was the first $\sqrt T$-regret guarantee for an RL algorithm with linear function approximation that needs neither a simulator nor any assumption beyond the linear structure.
--
--   **Formalization Note.** The constants $c$ (in $\beta$) and $C$ (hidden in the paper's $\mathcal O(\cdot)$) are fixed before the state and action spaces, $d$, $H$, $K$, $p$, the MDP and the run; the state, action and sample spaces range over `Type`. $d,H,K\ge1$ is assumed (it makes $\iota>0$). The finite action set carries a linear order used only to break ties in the argmax, and its discrete σ-algebra. The run is any process satisfying the protocol of the definition `LSVIUCB`: adapted states with transition law $\mathbb P_h(\cdot\mid x^k_h,a^k_h)$ given the past, actions chosen by Algorithm 1, and initial states otherwise unrestricted. $V^{\pi_k}_1$ is the model value of the greedy policy of episode $k$. "With probability $1-p$" is written as an upper bound $p$ on the outer measure of the event that the regret exceeds the bound. Assumption A is used with the total-variation normalization of the measures $\boldsymbol\mu_h$.
-- source:
--   Jin, Yang, Wang, Jordan, Provably Efficient Reinforcement Learning with Linear Function Approximation, arXiv:1907.05388v2, Theorem 3.1, p. 7 (restated p. 20)

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB
import Definitions.Def_LinearMDPRL_Linear_LinearMDP

namespace LinearMDPRL.Linear

open MeasureTheory ProbabilityTheory

/-- **Theorem 3.1** (Jin–Yang–Wang–Jordan, arXiv:1907.05388v2, p. 7). Under Assumption A there is
an absolute constant `c > 0` (and an absolute constant `C > 0` hidden in the `O(·)`) such that
for every linear MDP, every `p ∈ (0, 1)` and every run of LSVI-UCB with `λ = 1` and
`β = c · dH√ι`, `ι = log(2dT/p)`, `T = KH`, with probability at least `1 − p` the regret
satisfies `Regret(K) ≤ C √(d³H³Tι²)`. The constants are chosen before the state and action
spaces, the dimension, the horizon, the number of episodes, `p`, the MDP and the run. -/
theorem lsvi_ucb_regret :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {S A : Type} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
        [MeasurableSpace A] [DiscreteMeasurableSpace A] (d H K : ℕ), 1 ≤ d → 1 ≤ H → 1 ≤ K →
      ∀ (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)), IsLinearMDP M H d φ →
      ∀ p : ℝ, 0 < p → p < 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) (x : ℕ → ℕ → Ω → S) (a : ℕ → ℕ → Ω → A),
        IsLSVIUCBRun μ 𝓕 M φ 1 (fun _ => c * d * H * Real.sqrt (iota d K H p)) H K x a →
        μ {ω | C * Real.sqrt ((d : ℝ) ^ 3 * (H : ℝ) ^ 3 * ((K : ℝ) * H) * iota d K H p ^ 2) <
            regret M φ 1 (fun _ => c * d * H * Real.sqrt (iota d K H p)) H K
              (fun τ i => x τ i ω) (fun τ i => a τ i ω)}
          ≤ ENNReal.ofReal p := by sorry

end LinearMDPRL.Linear
