-- Prove2me | Theorems.Thm_OnlineLearningOCO_Agnostic_theorem_3_1
-- name    : OnlineLearningOCO.Agnostic.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:13.069603+00:00
-- url     : https://prove2.me/theorems/2c8f936b-e785-43a8-8445-80148c7022fc
-- title:
--   Theorem 3.1 — Weighted Majority with costs in [0,1] has regret log(d)/η + ηT, and 2√(log(d)T) with tuned η
-- statement:
--   Consider prediction with expert advice over $d \ge 1$ experts. On round $t = 1, 2, \dots$ an adversary reveals a cost vector $z_t \in [0,1]^d$. The **Weighted Majority** algorithm with parameter $\eta$ maintains the distribution
--
--   $$
--   w_1 = (1/d,\dots,1/d), \qquad w_{t+1}[i] = \frac{w_t[i]\, e^{-\eta z_t[i]}}{\sum_j w_t[j]\, e^{-\eta z_t[j]}},
--   $$
--
--   and pays the expected cost $\langle w_t, z_t\rangle$ on round $t$. Then for every horizon $T$:
--
--   1. for every $\eta > 0$,
--   $$\sum_{t=1}^T \langle w_t, z_t\rangle \le \min_{i\in[d]} \sum_{t=1}^T z_t[i] + \frac{\log d}{\eta} + \eta T;$$
--   2. for every $\eta \in (0,1)$,
--   $$\sum_{t=1}^T \langle w_t, z_t\rangle \le \frac{1}{1-\eta}\Big(\min_{i\in[d]} \sum_{t=1}^T z_t[i] + \frac{\log d}{\eta}\Big);$$
--   3. with $\eta = \sqrt{\log(d)/T}$,
--   $$\sum_{t=1}^T \langle w_t, z_t\rangle \le \min_{i\in[d]} \sum_{t=1}^T z_t[i] + 2\sqrt{\log(d)\, T};$$
--   4. with $\eta = 1/2$,
--   $$\sum_{t=1}^T \langle w_t, z_t\rangle \le 2\min_{i\in[d]} \sum_{t=1}^T z_t[i] + 4\log d.$$
--
--   Here $\log$ is the natural logarithm. This is the regret bound of the exponentially weighted forecaster on bounded costs; in §3.2.1 it is applied to the experts Expert$(i_1,\dots,i_L)$ to obtain Theorem 3.6.
--
--   **Formalization Note** The weights are the published `wmWeights η z t`, i.e. $w_t[i] \propto \exp(-\eta\sum_{s<t} z_s[i])$ with rounds indexed from $0$ (`wmWeights η z 0` is uniform). Each minimum over $i \in [d]$ is stated as "for every expert $i$", which is equivalent. The algorithm box restricts $\eta$ to $(0,1)$; bound 1 is stated for every $\eta > 0$ (its proof via Theorem 2.22 needs only $\eta > 0$) and bound 2 for $\eta\in(0,1)$. The tuned bound 3 is stated for every $d \ge 1$ and $T \ge 0$: when $d = 1$ or $T = 0$ the tuned value is $\eta = 0$, the weights are uniform, and the bound still holds.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 159, Theorem 3.1 (algorithm box Weighted Majority, p. 158)

import Mathlib
import Definitions.Def_UnderstandingML_Online

namespace OnlineLearningOCO.Agnostic

open UnderstandingML

/-- Theorem 3.1, p. 159. Weighted Majority (box on p. 158) over `d ≥ 1` experts with cost vectors
`z_t ∈ [0,1]^d`. Rounds are 0-based: `wmWeights η z t` is the paper's `w_{t+1}`, with
`wmWeights η z 0` uniform. For every expert `i` (equivalently, for the minimum over `i ∈ [d]`):
1. for every `η > 0`, `∑_t ⟨w_t, z_t⟩ ≤ ∑_t z_t[i] + log(d)/η + ηT`;
2. for every `η ∈ (0,1)`, `∑_t ⟨w_t, z_t⟩ ≤ (1/(1 − η)) (∑_t z_t[i] + log(d)/η)`;
3. with `η = √(log(d)/T)`, `∑_t ⟨w_t, z_t⟩ ≤ ∑_t z_t[i] + 2√(log(d) T)`;
4. with `η = 1/2`, `∑_t ⟨w_t, z_t⟩ ≤ 2 ∑_t z_t[i] + 4 log(d)`. -/
theorem theorem_3_1 {d : ℕ} (hd : 0 < d) (z : ℕ → Fin d → ℝ)
    (hz : ∀ t i, z t i ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    (∀ η : ℝ, 0 < η → ∀ i : Fin d,
      ∑ t ∈ Finset.range T, ∑ j, wmWeights η z t j * z t j ≤
        ∑ t ∈ Finset.range T, z t i + Real.log d / η + η * T) ∧
    (∀ η : ℝ, 0 < η → η < 1 → ∀ i : Fin d,
      ∑ t ∈ Finset.range T, ∑ j, wmWeights η z t j * z t j ≤
        (1 / (1 - η)) * (∑ t ∈ Finset.range T, z t i + Real.log d / η)) ∧
    (∀ i : Fin d,
      ∑ t ∈ Finset.range T, ∑ j, wmWeights (Real.sqrt (Real.log d / T)) z t j * z t j ≤
        ∑ t ∈ Finset.range T, z t i + 2 * Real.sqrt (Real.log d * T)) ∧
    (∀ i : Fin d,
      ∑ t ∈ Finset.range T, ∑ j, wmWeights (1 / 2) z t j * z t j ≤
        2 * ∑ t ∈ Finset.range T, z t i + 4 * Real.log d) := by sorry

end OnlineLearningOCO.Agnostic
