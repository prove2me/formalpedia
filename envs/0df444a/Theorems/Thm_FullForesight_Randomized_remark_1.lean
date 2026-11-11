-- Prove2me | Theorems.Thm_FullForesight_Randomized_remark_1
-- name    : FullForesight.Randomized.remark_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:17:12.561882+00:00
-- url     : https://prove2.me/theorems/36cb5049-a33f-4ac8-9b2f-88fecfe78395
-- title:
--   Remark 1 — the limiting impossibility: for fixed $C$, large $k$ caps the ratio at $\xi^\star + \delta$
-- statement:
--   For every consistency bound $C$ and every $\delta > 0$ there is $K$ such that for every $k \ge K$ there is an unweighted coverage instance with cardinality bound $k$ on which no valid $C$-consistent law of trajectories maintains an approximation ratio better than $\xi^\star + \delta$: for every such law and every $\alpha > \xi^\star + \delta$ there is a time $t$ with
--   $$\mathbb E[\mathrm{cov}_s(\mathrm{ALG}_t)] < \alpha\, \mathrm{cov}_s(\mathrm{OPT}_t).$$
--
--   Together with Theorem 2 this shows that $\xi^\star$ is the exact limit for consistent randomized clairvoyant algorithms.
--
--   Differences from the source:
--   - reading: "choosing $k$ sufficiently large" → there is $K$ such that every $k \ge K$ works; reason: the usual meaning of "sufficiently large".
--   - encoding: "no randomized C-consistent clairvoyant algorithm" on that instance → no valid C-consistent law of trajectories on it; reason: a clairvoyant algorithm run on one instance is a law of trajectories.
--   - encoding: coverage universe → finite subsets of $\mathbb N$, arrivals `Fin n`, approximation required also at $t = 0$; reason: every finite universe relabels into $\mathbb N$; coverage has $f(\emptyset) = 0$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…), p. 21, Remark 1

import Mathlib
import Definitions.Def_FullForesight_Randomized_Constants
import Definitions.Def_FullForesight_Randomized_Model
import Definitions.Def_FullForesight_Randomized_Coverage

namespace FullForesight.Randomized

theorem remark_1 :
    ∀ C δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∃ (n : ℕ) (s : Fin n → Finset ℕ), ∀ L : TrajLaw n, L.Valid k →
        L.Consistent C → ∀ α : ℝ, xiStar + δ < α → ¬ L.Approx (coverage s) k α := by sorry

end FullForesight.Randomized
