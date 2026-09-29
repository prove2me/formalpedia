-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_polynomial_drift
-- name    : MarkovChainCLT.clt_of_polynomial_drift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:37:19.691794+00:00
-- url     : https://prove2.me/theorems/270ddd57-3ff9-4b9a-9de3-ceb0b53c11f9
-- title:
--   CLT under polynomial drift: $\Delta V \le -dV^\tau + b\,\mathbb{1}_C$, $|f| \le V^{\tau+\eta-1}$ (Jones Thm 1(ii))
-- statement:
--   Let $X = \{X_n\}_{n \ge 0}$ be a Markov chain with transition kernel $P$ on a state space $\mathsf{X}$, Harris ergodic with invariant probability distribution $\pi$, and let $f : \mathsf{X} \to \mathbb{R}$ be measurable. Write $\bar f_n = n^{-1} \sum_{i=1}^{n} f(X_i)$ for the sample average and $E_\pi f = \int f \, d\pi$. Suppose $V : \mathsf{X} \to [1, \infty)$ is measurable, $C$ is a measurable small set, $d > 0$, $0 \le \tau < 1$, the polynomial drift condition
--
--   $$
--   PV(x) - V(x) \;\le\; -d\, V(x)^{\tau} + b\, \mathbb{1}_C(x) \qquad (x \in \mathsf{X})
--   $$
--
--   holds with $V$ integrable under every $P(x, \cdot)$, and $\eta$ satisfies $1 - \tau \le \eta \le 1$ together with $E_\pi V^{2\eta} < \infty$ and $|f| \le V^{\tau + \eta - 1}$ pointwise.
--
--   Then the chain satisfies the central limit theorem for $f$: there is a single asymptotic variance $\sigma_f^2 \ge 0$ such that for every initial distribution of the chain,
--
--   $$
--   \sqrt{n}\,\bigl(\bar f_n - E_\pi f\bigr) \xrightarrow{d} N(0, \sigma_f^2) \qquad (n \to \infty).
--   $$
--
--   This extends the drift route to chains converging only at a polynomial rate (Jarner–Roberts, Theorem 4.2), the regime of many heavy-tailed MCMC samplers.
--
--   **Formalization Note** "Harris ergodic" is encoded by its total-variation characterization: $\pi$ is invariant for $P$ and $\|P^n(x, \cdot) - \pi\| \to 0$ for every starting point $x$ (equivalent to the classical aperiodic, $\psi$-irreducible, positive Harris recurrent definition; the "every $x$" quantifier is exactly the Harris property). Convergence in distribution is weak convergence of laws, and $N(0, 0)$ is read as the point mass at $0$, which absorbs the source's "$\sigma_f^2 > 0$" caveat. The $\sigma$-algebra of the state space is additionally assumed countably generated, the standard general-state-space setting of Meyn and Tweedie.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorem 1, condition 2 (arXiv v2 p. 4, eq. (6) drift); original: S. F. Jarner & G. O. Roberts, Polynomial convergence rates of Markov chains, Ann. Appl. Probab. 12 (2002), Theorem 4.2

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovDriftMinorization
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Theorem 1, condition 2** (Jarner–Roberts 2002, Theorem 4.2): a Harris ergodic
chain satisfying the polynomial drift condition towards a small set, with
`|f| ≤ V^{τ+η-1}` for some `1 - τ ≤ η ≤ 1` such that `E_π V^{2η} < ∞`,
satisfies the CLT for every initial distribution. -/

theorem MarkovChainCLT.clt_of_polynomial_drift {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (V : X → ℝ) (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (C : Set X) (hC : MeasurableSet C) (hsmall : IsSmallSet P C)
    (d b τ : ℝ) (hd : 0 < d) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hdrift : PolyDriftCondition P V d b τ C)
    (η : ℝ) (hη0 : 1 - τ ≤ η) (hη1 : η ≤ 1)
    (hVint : Integrable (fun x => V x ^ (2 * η)) π)
    (hfV : ∀ x, |f x| ≤ V x ^ (τ + η - 1)) :
    SatisfiesCLT P π f := by sorry
