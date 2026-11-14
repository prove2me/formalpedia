-- Prove2me | Theorems.Thm_FullForesight_Randomized_main_result_1
-- name    : FullForesight.Randomized.main_result_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T06:17:09.112134+00:00
-- url     : https://prove2.me/theorems/ca966206-8050-4b90-bc41-a930472070c8
-- title:
--   Main Result 1 — the tight randomized bound $\xi^\star \approx 0.7942$ for consistent clairvoyant submodular maximization
-- statement:
--   Let $\Psi(\xi) = 89\xi^4 - 44\xi^3 - 19\xi^2 - 3\xi + 1$ and let $\xi^\star$ be as defined. Then:
--
--   **(0)** $\xi^\star \in (1/2, 1)$, $\Psi(\xi^\star) = 0$, $\xi^\star$ is the only root of $\Psi$ in $(1/2, 1)$, and $|\xi^\star - 0.7942| < 0.00005$.
--
--   **(a)** There is a universal constant $c$ such that for every $\varepsilon \in (0, 1)$ and every instance of clairvoyant monotone submodular maximization under a cardinality constraint ($n$ arrivals, any $k \ge 1$, $f \ge 0$ monotone submodular, no normalization) there is a valid law of solution trajectories that is $c\varepsilon^{-2}$-consistent on every realization and satisfies
--   $$\mathbb E[f(\mathrm{ALG}_t)] \ge (\xi^\star - \varepsilon)\, f(\mathrm{OPT}_t) \qquad (t = 0, \dots, n).$$
--
--   **(b)** For every consistency bound $C$ and every $\alpha > \xi^\star$ there is an unweighted coverage instance (cardinality bound $k \ge 1$) on which no valid $C$-consistent law of trajectories is an $\alpha$-approximation: each such law has a time $t$ with $\mathbb E[\mathrm{cov}_s(\mathrm{ALG}_t)] < \alpha\, \mathrm{cov}_s(\mathrm{OPT}_t)$.
--
--   So $\xi^\star$ is the optimal approximation ratio of consistent randomized clairvoyant algorithms, for monotone submodular functions and already for coverage functions.
--
--   Differences from the source:
--   - reading: "$\xi^\star \approx 0.7942$" and footnote ‡ ("the unique root in $(1/2,1)$ of Ψ") → clause (0): $\xi^\star \in (1/2,1)$, $\Psi(\xi^\star) = 0$, uniqueness, $|\xi^\star - 0.7942| < 0.00005$; reason: $\xi^\star$ is a concrete definition, so its defining property is part of the conclusion, and the ≈ is given the meaning "rounds to 0.7942".
--   - encoding: "there is a randomized clairvoyant algorithm … $O(\varepsilon^{-2})$-consistent" → a universal $c$, chosen before $\varepsilon$ and the instance, and for every instance a valid $c\varepsilon^{-2}$-consistent law of trajectories; reason: a clairvoyant algorithm with unrestricted computation is a per-instance law of trajectories; $O(\cdot)$ is an absolute constant.
--   - encoding: "no consistent randomized clairvoyant algorithm can achieve a ratio greater than $\xi^\star$, even for coverage functions" → for every $C$ and $\alpha > \xi^\star$ some unweighted coverage instance has no valid $C$-consistent $\alpha$-approximate law; reason: an algorithm is a per-instance choice of law, so "no algorithm is α-approximate on every coverage instance" is "some coverage instance has no α-approximate law"; consistent means $C$-consistent for some constant $C$.
--   - encoding: arrivals → `Fin n` in arrival order, coverage universe → finite subsets of $\mathbb N$, approximation required also at $t = 0$; reason: distinct arrivals and finite universes relabel; at $t = 0$ both sides are $f(\emptyset)$ times a factor $\le 1$ in (a), and $0$ for coverage in (b).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…), p. 2, Main Result 1 and footnote ‡ (combining Theorem 1, Theorem 2, Proposition 1 and Remark 1)

import Mathlib
import Definitions.Def_FullForesight_Randomized_Constants
import Definitions.Def_FullForesight_Randomized_Model
import Definitions.Def_FullForesight_Randomized_Coverage

namespace FullForesight.Randomized

theorem main_result_1 :
    ((1 / 2 : ℝ) < xiStar ∧ xiStar < 1 ∧ Psi xiStar = 0 ∧
        (∀ ξ ∈ Set.Ioo (1 / 2 : ℝ) 1, Psi ξ = 0 → ξ = xiStar) ∧
        |xiStar - 0.7942| < 0.00005) ∧
      (∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∀ (n k : ℕ) (f : Finset (Fin n) → ℝ), IsInstance k f →
          ∃ L : TrajLaw n, L.Valid k ∧ L.Consistent (c / ε ^ 2) ∧
            L.Approx f k (xiStar - ε)) ∧
      (∀ C α : ℝ, xiStar < α →
        ∃ (n k : ℕ) (s : Fin n → Finset ℕ), 1 ≤ k ∧
          ∀ L : TrajLaw n, L.Valid k → L.Consistent C → ¬ L.Approx (coverage s) k α) := by sorry

end FullForesight.Randomized
