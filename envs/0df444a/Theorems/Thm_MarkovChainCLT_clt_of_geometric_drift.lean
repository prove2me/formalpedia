-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_geometric_drift
-- name    : MarkovChainCLT.clt_of_geometric_drift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:37:00.550313+00:00
-- url     : https://prove2.me/theorems/306878d6-ef77-4f2a-916a-ef5db1fa064c
-- title:
--   CLT under geometric drift: $\Delta V \le -dV + b\,\mathbb{1}_C$, $f^2 \le V$ (Jones Thm 1(i))
-- statement:
--   Let $X = \{X_n\}_{n \ge 0}$ be a Markov chain with transition kernel $P$ on a state space $\mathsf{X}$, Harris ergodic with invariant probability distribution $\pi$, and let $f : \mathsf{X} \to \mathbb{R}$ be measurable. Write $\bar f_n = n^{-1} \sum_{i=1}^{n} f(X_i)$ for the sample average and $E_\pi f = \int f \, d\pi$. Suppose $V : \mathsf{X} \to [1, \infty)$ is measurable, $C$ is a measurable small set, $d > 0$ and $b$ are constants, the geometric drift condition
--
--   $$
--   PV(x) - V(x) \;\le\; -d\, V(x) + b\, \mathbb{1}_C(x) \qquad (x \in \mathsf{X})
--   $$
--
--   holds with $V$ integrable under every $P(x, \cdot)$, and $f^2 \le V$ pointwise.
--
--   Then the chain satisfies the central limit theorem for $f$: there is a single asymptotic variance $\sigma_f^2 \ge 0$ such that for every initial distribution of the chain,
--
--   $$
--   \sqrt{n}\,\bigl(\bar f_n - E_\pi f\bigr) \xrightarrow{d} N(0, \sigma_f^2) \qquad (n \to \infty).
--   $$
--
--   This is the workhorse CLT of applied Markov chain Monte Carlo: drift towards a small set is the standard checkable route to a CLT for a specific sampler (Meyn–Tweedie, Theorem 17.0.1).
--
--   **Formalization Note** "Harris ergodic" is encoded by its total-variation characterization: $\pi$ is invariant for $P$ and $\|P^n(x, \cdot) - \pi\| \to 0$ for every starting point $x$ (equivalent to the classical aperiodic, $\psi$-irreducible, positive Harris recurrent definition; the "every $x$" quantifier is exactly the Harris property). Convergence in distribution is weak convergence of laws, and $N(0, 0)$ is read as the point mass at $0$, which absorbs the source's "$\sigma_f^2 > 0$" caveat. The $\sigma$-algebra of the state space is additionally assumed countably generated, the standard general-state-space setting of Meyn and Tweedie.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorem 1, condition 1 (arXiv v2 p. 4, eq. (5) drift); original: S. P. Meyn & R. L. Tweedie, Markov Chains and Stochastic Stability (1993), Theorem 17.0.1

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovDriftMinorization
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Theorem 1, condition 1** (Meyn–Tweedie 1993, Theorem 17.0.1): a Harris ergodic
chain satisfying the geometric drift condition towards a small set, with
`f² ≤ V`, satisfies the CLT for every initial distribution. -/

theorem MarkovChainCLT.clt_of_geometric_drift {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (V : X → ℝ) (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (C : Set X) (hC : MeasurableSet C) (hsmall : IsSmallSet P C)
    (d b : ℝ) (hd : 0 < d) (hdrift : GeoDriftCondition P V d b C)
    (hfV : ∀ x, f x ^ 2 ≤ V x) :
    SatisfiesCLT P π f := by sorry
