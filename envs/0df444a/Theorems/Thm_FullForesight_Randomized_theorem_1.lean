-- Prove2me | Theorems.Thm_FullForesight_Randomized_theorem_1
-- name    : FullForesight.Randomized.theorem_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T06:17:18.196767+00:00
-- url     : https://prove2.me/theorems/eaed4fc0-636d-4b4b-adfe-474ba3c5ea25
-- title:
--   Theorem 1 — $\varepsilon k$-consistency caps the ratio at $\xi^\star + O(\varepsilon)$ on Maximum Coverage
-- statement:
--   There is a universal constant $c$ such that for every cardinality bound $k \ge 1$, every $\varepsilon \in [1/k, 1]$ and every $\alpha > \xi^\star + c\varepsilon$ there is an unweighted coverage instance with cardinality bound $k$ (sets $s_0, \dots, s_{n-1}$, $f = \mathrm{cov}_s$) on which no valid $\varepsilon k$-consistent law of trajectories is an $\alpha$-approximation: for each such law there is a time $t$ with
--   $$\mathbb E[\mathrm{cov}_s(\mathrm{ALG}_t)] < \alpha\, \mathrm{cov}_s(\mathrm{OPT}_t).$$
--
--   So no randomized $\varepsilon k$-consistent clairvoyant algorithm achieves a ratio better than $\xi^\star + O(\varepsilon)$ for Maximum Coverage.
--
--   Differences from the source:
--   - encoding: "no randomized εk-consistent clairvoyant algorithm can achieve an approximation ratio better than ξ⋆ + O(ε) for Maximum Coverage subject to k" → ∃ universal $c$; for every $\alpha > \xi^\star + c\varepsilon$ some coverage instance with bound $k$ has no valid $\varepsilon k$-consistent $\alpha$-approximate law; reason: a clairvoyant algorithm is a per-instance choice of law, so "no algorithm is α-approximate on all instances" is "some instance has no α-approximate law"; O(ε) is $c\varepsilon$ with an absolute $c$.
--   - reading: "≈ 0.7942 + O(ε)" → dropped; reason: a display approximation of $\xi^\star$, whose value is fixed by Proposition 1.
--   - encoding: Maximum Coverage → unweighted coverage of finite subsets of $\mathbb N$ arriving as `Fin n`; approximation required also at $t = 0$; reason: every finite universe relabels into $\mathbb N$; coverage has $f(\emptyset) = 0$, so $t = 0$ adds no constraint.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…), p. 5, Theorem 1 (restated and proved pp. 19–21)

import Mathlib
import Definitions.Def_FullForesight_Randomized_Constants
import Definitions.Def_FullForesight_Randomized_Model
import Definitions.Def_FullForesight_Randomized_Coverage

namespace FullForesight.Randomized

theorem theorem_1 :
    ∃ c : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 1 / (k : ℝ) ≤ ε → ε ≤ 1 →
      ∀ α : ℝ, xiStar + c * ε < α →
        ∃ (n : ℕ) (s : Fin n → Finset ℕ), ∀ L : TrajLaw n, L.Valid k →
          L.Consistent (ε * k) → ¬ L.Approx (coverage s) k α := by sorry

end FullForesight.Randomized
