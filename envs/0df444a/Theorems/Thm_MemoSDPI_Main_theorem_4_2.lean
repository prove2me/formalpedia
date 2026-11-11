-- Prove2me | Theorems.Thm_MemoSDPI_Main_theorem_4_2
-- name    : MemoSDPI.Main.theorem_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:43:00.526262+00:00
-- url     : https://prove2.me/theorems/efd22192-1794-4a89-9b1b-acec0a4bb13e
-- title:
--   Theorem 4.2 — accurate top-k selection under a probit-normal prior carries k log(m/k)/32 nats about θ and memorizes k log²(m/k)/(2048 n α²)
-- statement:
--   Let $m, k, n$ be positive integers with $m/k \ge e^{64}$, let $0 < \alpha \le 1/16$, and set
--   $$
--   \sigma = \frac{8\alpha}{\sqrt{\log(m/k)}}.
--   $$
--   Let $\theta$ be drawn from the product probit-normal prior of scale $\sigma$ on $[0,1]^m$; conditional on $\theta$, let $S$ consist of $n$ independent samples from the product Bernoulli distribution with mean $\theta$, and let $P$ be the resulting average-case problem. If an algorithm $A$ returns a $k$-element set and
--   $$
--   \Pr\Big[\min_{j\in A(S)}\theta_j \ge \theta_{(k)} - \alpha\Big] \;\ge\; \frac{19}{20},
--   $$
--   the probability being over $\theta$, $S$ and the randomness of $A$, then
--   $$
--   I(A(S);\theta) \;\ge\; \frac{k\log(m/k)}{32} \tag{4.2}
--   $$
--   and
--   $$
--   \mathrm{mem}_n(A, P) \;\ge\; \frac{k\log^2(m/k)}{2048\, n\alpha^2}. \tag{4.3}
--   $$
--   Natural logarithms; $\theta_{(k)}$ is the $k$-th largest coordinate of $\theta$. Combined with information upper bounds for private and replicable algorithms, (4.3) gives Theorem 7.4.
--
--   **Formalization Note** $A$ is a `DPVerify.RandAlg` on samples of length $n$ over `Fin m → Bool` with outputs in `KSubset m k`. The success probability is the measure of the success set under the joint law of $(\theta, S, \text{seed})$. $\sigma$ is a variable constrained by the displayed equation. The bounds enter $[0,\infty]$ through `ENNReal.ofReal`.
--
--   Differences from the source:
--   - encoding: A returns a k-element set → output type KSubset m k; reason: every output is a k-subset by type
--   - encoding: min_{j∈A(S)} θ_j ≥ θ_(k) − α → θ_j ≥ θ_(k) − α for every j ∈ A(S) (selectionSuccess); reason: equal for the nonempty k-sets, k ≥ 1
--   - encoding: real lower bounds on informations in [0, ∞] → ENNReal.ofReal (bound) ≤ I; reason: the bounds are positive; same meaning
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 16, Theorem 4.2

import Mathlib
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_MemoSDPI_Main_Memorization
import Definitions.Def_MemoSDPI_Main_ProductBernoulli
import Definitions.Def_MemoSDPI_Main_Selection

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MemoSDPI.Main

/-- Feldman, Lyu, Talwar, *Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities*, STOC 2027 submission (manuscript sha256 dbb300da…), p. 16, Theorem 4.2: with `m/k ≥ e^64`, `0 < α ≤ 1/16`, `σ = 8α/√log(m/k)`, `θ` from the
product probit-normal prior of scale `σ` on `[0, 1]^m` and `S` made of `n` samples of the product
Bernoulli law with mean `θ`: if `A` returns `k`-sets and
`Pr[min_{j∈A(S)} θ_j ≥ θ_(k) − α] ≥ 19/20` (over `θ`, `S` and the seed), then
`I(A(S); θ) ≥ k log(m/k)/32` (4.2) and `mem_n(A, P) ≥ k log²(m/k)/(2048 n α²)` (4.3). -/
theorem theorem_4_2 (m k n : ℕ) (hm : 0 < m) (hk : 0 < k) (hn : 0 < n)
    (hmk : Real.exp 64 ≤ (m : ℝ) / k) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1 / 16)
    (σ : ℝ) (hσ : σ = 8 * α / Real.sqrt (Real.log ((m : ℝ) / k)))
    (A : DPVerify.RandAlg (Fin m → Bool) (KSubset m k) n)
    (hacc : ENNReal.ofReal (19 / 20) ≤
      algJointLaw A (probitPrior σ m) prodBernoulli
        {q | selectionSuccess q.1.1 α (A.run q.1.2 q.2)}) :
    ENNReal.ofReal ((k : ℝ) * Real.log ((m : ℝ) / k) / 32) ≤
        infoParam A (probitPrior σ m) prodBernoulli ∧
      ENNReal.ofReal ((k : ℝ) * Real.log ((m : ℝ) / k) ^ 2 / (2048 * (n : ℝ) * α ^ 2)) ≤
        memAvg A (probitPrior σ m) prodBernoulli := by sorry

end MemoSDPI.Main
