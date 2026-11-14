-- Prove2me | Theorems.Thm_FullForesight_Deterministic_main_result_2
-- name    : FullForesight.Deterministic.main_result_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-13T15:08:26.663019+00:00
-- url     : https://prove2.me/theorems/5c943e2d-f379-4081-8d98-d56a1298402d
-- title:
--   Main Result 2 — the tight deterministic bound $3/4$ for consistent clairvoyant submodular maximization
-- statement:
--   This is the second main result of the paper: for **deterministic** clairvoyant algorithms, the optimal approximation ratio achievable with constantly many changes per arrival is exactly $3/4$.
--
--   Elements $0, \dots, n-1$ arrive in this order and $X_t$ is the set of the first $t$ of them. An instance is a cardinality bound $k \ge 1$ and a nonnegative monotone submodular function $f$ on subsets of the elements; $f(\mathrm{OPT}_t) = \max\{f(S) : S \subseteq X_t, |S| \le k\}$. A deterministic clairvoyant algorithm, which knows the whole instance in advance, produces a trajectory $\mathrm{ALG}_0 = \emptyset, \mathrm{ALG}_1, \dots, \mathrm{ALG}_n$ with $\mathrm{ALG}_t \subseteq X_t$ and $|\mathrm{ALG}_t| \le k$. It is $C$-consistent if $|\mathrm{ALG}_t \triangle \mathrm{ALG}_{t-1}| \le C$ for all $t \ge 1$, and an $\alpha$-approximation if $f(\mathrm{ALG}_t) \ge \alpha f(\mathrm{OPT}_t)$ at every time $t$.
--
--   **(a) Algorithm.** There is a universal constant $c$ such that for every $\varepsilon \in (0,1)$ and every instance ($n$ arrivals, any $k \ge 1$, $f \ge 0$ monotone submodular) there is a valid trajectory that is $c\,\varepsilon^{-3}\log(1/\varepsilon)$-consistent and satisfies
--   $$f(\mathrm{ALG}_t) \ge \left(\tfrac34 - \varepsilon\right) f(\mathrm{OPT}_t) \qquad (t = 0, \dots, n).$$
--
--   **(b) Impossibility.** For every consistency bound $C$ and every $\alpha > 3/4$ there is an unweighted coverage instance (sets $s_0, \dots, s_{n-1}$ arriving in order, $f(S) = |\bigcup_{i \in S} s_i|$, cardinality bound $k \ge 1$) on which no valid $C$-consistent trajectory is an $\alpha$-approximation: each such trajectory has a time $t$ with $f(\mathrm{ALG}_t) < \alpha f(\mathrm{OPT}_t)$.
--
--   So $3/4$ is the optimal approximation ratio of consistent deterministic clairvoyant algorithms, for monotone submodular functions and already for coverage functions. Together with Main Result 1 (the randomized threshold $\xi^\star \approx 0.7942$) it shows that randomization strictly helps in this model.
--
--   Differences from the source:
--   - encoding: "there is a deterministic clairvoyant algorithm … that is $O(\varepsilon^{-3}\log(1/\varepsilon))$-consistent" → a universal $c$, chosen before $\varepsilon$ and the instance, and for every instance a valid $c\,\varepsilon^{-3}\log(1/\varepsilon)$-consistent trajectory; reason: a clairvoyant algorithm with unrestricted computation is a per-instance choice of trajectory, and $O(\cdot)$ is an absolute constant. This is the same encoding as in the published Main Result 1.
--   - encoding: "no consistent deterministic clairvoyant algorithm can achieve an approximation ratio greater than $3/4$, even for coverage functions" → for every $C$ and $\alpha > 3/4$ some unweighted coverage instance has no valid $C$-consistent $\alpha$-approximate trajectory; reason: "consistent" means $C$-consistent for some constant $C$ independent of the instance (p. 1), and "no algorithm is $\alpha$-approximate on every coverage instance" is "some coverage instance has no $\alpha$-approximate trajectory".
--   - encoding: arrivals → `Fin n` in arrival order, coverage universe → finite subsets of $\mathbb N$, approximation required also at $t = 0$; reason: distinct arrivals and finite universes relabel; at $t = 0$ both sides are $f(\emptyset)$ times a factor at most $1$ in (a), and $0$ for coverage in (b).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…56df), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/862.pdf, p. 3, Main Result 2 (combining Theorem 3, p. 10, and Theorem 4, p. 11)

import Mathlib
import Definitions.Def_FullForesight_Randomized_Model
import Definitions.Def_FullForesight_Randomized_Coverage
import Definitions.Def_FullForesight_Deterministic_Model

open FullForesight.Randomized

namespace FullForesight.Deterministic

theorem main_result_2 :
    (∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∀ (n k : ℕ) (f : Finset (Fin n) → ℝ), IsInstance k f →
          ∃ A : Fin (n + 1) → Finset (Fin n), IsValid A k ∧
            IsConsistent A (c / ε ^ 3 * Real.log (1 / ε)) ∧ IsApprox A f k (3 / 4 - ε)) ∧
      (∀ C α : ℝ, 3 / 4 < α →
        ∃ (n k : ℕ) (s : Fin n → Finset ℕ), 1 ≤ k ∧
          ∀ A : Fin (n + 1) → Finset (Fin n), IsValid A k → IsConsistent A C →
            ¬ IsApprox A (coverage s) k α) := by sorry

end FullForesight.Deterministic
