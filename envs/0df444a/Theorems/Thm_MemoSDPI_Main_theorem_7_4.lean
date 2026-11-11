-- Prove2me | Theorems.Thm_MemoSDPI_Main_theorem_7_4
-- name    : MemoSDPI.Main.theorem_7_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:43:29.826251+00:00
-- url     : https://prove2.me/theorems/ff41402a-7bb5-4be1-96d9-8bdee4352e3e
-- title:
--   Theorem 7.4 — sample lower bounds for (ε, δ)-private and ρ-replicable top-k selection
-- statement:
--   Let $m, k$ be positive integers with $m/k \ge e^{64}$ and let $0 < \alpha \le 1/16$. Suppose that an algorithm $A$ uses $n$ samples and solves $(m,k)$-selection with accuracy $\alpha$ and failure probability at most $1/100$ for every product Bernoulli distribution on $\{0,1\}^m$: for every $\theta \in [0,1]^m$ it returns a $k$-set $T\subseteq[m]$ with $\Pr[\min_{j\in T}\theta_j \ge \theta_{(k)} - \alpha] \ge 99/100$, over $S \sim (\mathrm{Ber}(\theta_1)\otimes\cdots\otimes\mathrm{Ber}(\theta_m))^n$ and the randomness of $A$.
--
--   If $A$ is $(\varepsilon,\delta)$-differentially private with $0 < \varepsilon \le 1$ (and $\delta\in[0,1]$), then
--   $$
--   n^2 \;\ge\; \frac{k\log^2(m/k)}{2048\,\alpha^2\big(\varepsilon^2/2 + \delta(m\log 2 + 3)\big)},
--   $$
--   and if moreover $\delta(m\log 2 + 3) \le \varepsilon^2/2$, then
--   $$
--   n \;\ge\; \frac{\sqrt{k}\,\log(m/k)}{46\,\alpha\varepsilon}.
--   $$
--   If $A$ is $\rho$-replicable on this family for some $0 < \rho \le 1/100$, then
--   $$
--   n \;\ge\; \frac{k\log^2(m/k)}{8192\,\alpha^2\rho\log(1/\rho)}.
--   $$
--   Natural logarithms. For a constant replicability parameter, selecting $k$ of $m$ coordinates with accuracy $\alpha$ requires $\Omega(k\log^2(m/k)/\alpha^2)$ samples, while the private bound recovers the $\sqrt{k}\log(m/k)$ dependence known for constant accuracy.
--
--   **Formalization Note** $A$ is a `DPVerify.RandAlg` on samples of length $n$ over $\{0,1\}^m$ = `Fin m → Bool` with outputs in `KSubset m k` (a $k$-subset on every sample and seed); accuracy is the mission's `SolvesSelection A α (1/100)`, required for every `θ : Fin m → unitInterval`. Differential privacy is the published `DPVerify.IsDPAlg` (replacement adjacency). Replicability "on this family" is `IsReplicableOn` over the set of all product Bernoulli distributions `Set.range prodBernoulliPM`. $n$ is any natural number; for $n = 0$ the accuracy hypothesis cannot hold.
--
--   Differences from the source:
--   - encoding: an algorithm that returns a set T ⊆ [m] of size k → A : DPVerify.RandAlg (Fin m → Bool) (KSubset m k) n; reason: outputs are k-subsets on every sample and seed by type
--   - encoding: (ε, δ)-differentially private (p. 24 definition, δ ∈ [0, 1]) → DPVerify.IsDPAlg A ε δ with hypotheses 0 ≤ δ ≤ 1; reason: the p. 24 definition fixes δ ∈ [0, 1]; replacement adjacency as in the published predicate
--   - encoding: ρ-replicable on the family of product Bernoulli distributions → IsReplicableOn A (Set.range prodBernoulliPM) ρ, i.e. IsReplicableAt at every θ ∈ [0, 1]^m; reason: Definition 6.3 on this family
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 31, Theorem 7.4

import Mathlib
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_DPVerify_IsDPAlg
import Definitions.Def_DPVerify_IsReplicableAt
import Definitions.Def_MemoSDPI_Main_ProductBernoulli
import Definitions.Def_MemoSDPI_Main_Selection
import Definitions.Def_MemoSDPI_Main_IsReplicableOn

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MemoSDPI.Main

/-- Feldman, Lyu, Talwar, *Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities*, STOC 2027 submission (manuscript sha256 dbb300da…), p. 31, Theorem 7.4: with `m/k ≥ e^64` and `0 < α ≤ 1/16`, an algorithm on `n` samples
that solves `(m, k)`-selection with accuracy `α` and failure probability at most `1/100` for every
product Bernoulli distribution on `{0,1}^m` satisfies: if it is `(ε, δ)`-DP with `0 < ε ≤ 1`, then
`n² ≥ k log²(m/k)/(2048 α² (ε²/2 + δ(m log 2 + 3)))`, and, if moreover `δ(m log 2 + 3) ≤ ε²/2`,
`n ≥ √k log(m/k)/(46 α ε)`; if it is `ρ`-replicable on this family with `0 < ρ ≤ 1/100`, then
`n ≥ k log²(m/k)/(8192 α² ρ log(1/ρ))`. -/
theorem theorem_7_4 (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (hmk : Real.exp 64 ≤ (m : ℝ) / k)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1 / 16) (n : ℕ)
    (A : DPVerify.RandAlg (Fin m → Bool) (KSubset m k) n)
    (hacc : SolvesSelection A α (1 / 100)) :
    (∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 ≤ δ → δ ≤ 1 → DPVerify.IsDPAlg A ε δ →
        (k : ℝ) * Real.log ((m : ℝ) / k) ^ 2 /
            (2048 * α ^ 2 * (ε ^ 2 / 2 + δ * ((m : ℝ) * Real.log 2 + 3))) ≤ (n : ℝ) ^ 2 ∧
          (δ * ((m : ℝ) * Real.log 2 + 3) ≤ ε ^ 2 / 2 →
            Real.sqrt k * Real.log ((m : ℝ) / k) / (46 * α * ε) ≤ (n : ℝ))) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 100 → IsReplicableOn A (Set.range prodBernoulliPM) ρ →
        (k : ℝ) * Real.log ((m : ℝ) / k) ^ 2 / (8192 * α ^ 2 * ρ * Real.log (1 / ρ)) ≤
          (n : ℝ)) := by sorry

end MemoSDPI.Main
