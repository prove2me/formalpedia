-- Prove2me | Theorems.Thm_FullForesight_main_results
-- name    : FullForesight.main_results
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-13T15:09:07.307745+00:00
-- url     : https://prove2.me/theorems/9a54db04-d4c5-48c1-bf9b-7c1287605395
-- title:
--   Main Results 1 and 2 — the tight bounds $\xi^\star \approx 0.7942$ (randomized) and $3/4$ (deterministic) for consistent clairvoyant submodular maximization
-- statement:
--   This theorem is the conjunction of the two main results of the paper. It determines the optimal approximation ratio of consistent clairvoyant algorithms for monotone submodular maximization under a cardinality constraint, both for randomized and for deterministic algorithms.
--
--   Elements $0, \dots, n-1$ arrive in this order and $X_t$ is the set of the first $t$ of them. An instance is a cardinality bound $k \ge 1$ and a nonnegative monotone submodular function $f$; $f(\mathrm{OPT}_t) = \max\{f(S) : S \subseteq X_t, |S| \le k\}$. A clairvoyant algorithm knows the instance in advance and maintains solutions $\mathrm{ALG}_0 = \emptyset, \mathrm{ALG}_1, \dots, \mathrm{ALG}_n$ with $\mathrm{ALG}_t \subseteq X_t$, $|\mathrm{ALG}_t| \le k$. It is $C$-consistent if $|\mathrm{ALG}_t \triangle \mathrm{ALG}_{t-1}| \le C$ for all $t \ge 1$ (on every realization, if randomized). Let $\Psi(\xi) = 89\xi^4 - 44\xi^3 - 19\xi^2 - 3\xi + 1$.
--
--   **Main Result 1 (randomized).**
--
--   1. $\xi^\star \in (1/2, 1)$, $\Psi(\xi^\star) = 0$, $\xi^\star$ is the only root of $\Psi$ in $(1/2,1)$, and $|\xi^\star - 0.7942| < 0.00005$.
--   2. There is a universal constant $c$ such that for every $\varepsilon \in (0,1)$ and every instance there is a valid, $c\,\varepsilon^{-2}$-consistent law of solution trajectories with
--   $$\mathbb E[f(\mathrm{ALG}_t)] \ge (\xi^\star - \varepsilon)\, f(\mathrm{OPT}_t) \qquad (t = 0, \dots, n).$$
--   3. For every $C$ and every $\alpha > \xi^\star$ there is an unweighted coverage instance on which no valid $C$-consistent law of trajectories is an $\alpha$-approximation in expectation.
--
--   **Main Result 2 (deterministic).**
--
--   4. There is a universal constant $c$ such that for every $\varepsilon \in (0,1)$ and every instance there is a valid, $c\,\varepsilon^{-3}\log(1/\varepsilon)$-consistent trajectory with
--   $$f(\mathrm{ALG}_t) \ge \left(\tfrac34 - \varepsilon\right) f(\mathrm{OPT}_t) \qquad (t = 0, \dots, n).$$
--   5. For every $C$ and every $\alpha > 3/4$ there is an unweighted coverage instance on which no valid $C$-consistent trajectory is an $\alpha$-approximation.
--
--   The two thresholds, $\xi^\star \approx 0.7942$ and $3/4$, are the information-theoretic limits of consistency with full foresight; they hold for monotone submodular functions and already for coverage functions.
--
--   **Formalization Note** The statement is literally the conjunction of the two published theorems `FullForesight.Randomized.main_result_1` and `FullForesight.Deterministic.main_result_2`, with the same encodings; see those theorems for the differences from the source.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…56df), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/862.pdf, p. 2, Main Result 1 and footnote ‡; p. 3, Main Result 2

import Mathlib
import Definitions.Def_FullForesight_Randomized_Constants
import Definitions.Def_FullForesight_Randomized_Model
import Definitions.Def_FullForesight_Randomized_Coverage
import Definitions.Def_FullForesight_Deterministic_Model

open FullForesight.Randomized FullForesight.Deterministic

namespace FullForesight

theorem main_results :
    (((1 / 2 : ℝ) < xiStar ∧ xiStar < 1 ∧ Psi xiStar = 0 ∧
        (∀ ξ ∈ Set.Ioo (1 / 2 : ℝ) 1, Psi ξ = 0 → ξ = xiStar) ∧
        |xiStar - 0.7942| < 0.00005) ∧
      (∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∀ (n k : ℕ) (f : Finset (Fin n) → ℝ), IsInstance k f →
          ∃ L : TrajLaw n, L.Valid k ∧ L.Consistent (c / ε ^ 2) ∧
            L.Approx f k (xiStar - ε)) ∧
      (∀ C α : ℝ, xiStar < α →
        ∃ (n k : ℕ) (s : Fin n → Finset ℕ), 1 ≤ k ∧
          ∀ L : TrajLaw n, L.Valid k → L.Consistent C → ¬ L.Approx (coverage s) k α)) ∧
    ((∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∀ (n k : ℕ) (f : Finset (Fin n) → ℝ), IsInstance k f →
          ∃ A : Fin (n + 1) → Finset (Fin n), IsValid A k ∧
            IsConsistent A (c / ε ^ 3 * Real.log (1 / ε)) ∧ IsApprox A f k (3 / 4 - ε)) ∧
      (∀ C α : ℝ, 3 / 4 < α →
        ∃ (n k : ℕ) (s : Fin n → Finset ℕ), 1 ≤ k ∧
          ∀ A : Fin (n + 1) → Finset (Fin n), IsValid A k → IsConsistent A C →
            ¬ IsApprox A (coverage s) k α)) := by sorry

end FullForesight
