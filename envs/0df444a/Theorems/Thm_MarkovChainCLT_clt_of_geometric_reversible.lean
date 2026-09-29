-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_geometric_reversible
-- name    : MarkovChainCLT.clt_of_geometric_reversible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:41:50.869113+00:00
-- url     : https://prove2.me/theorems/40bc603c-31c7-49b8-b596-33cd9ddf296e
-- title:
--   Roberts–Rosenthal CLT: geometric ergodicity + detailed balance + $E_\pi f^2 < \infty$ (Jones Cor 4)
-- statement:
--   Let $X = \{X_n\}_{n \ge 0}$ be a Markov chain with transition kernel $P$ on a state space $\mathsf{X}$, Harris ergodic with invariant probability distribution $\pi$, and let $f : \mathsf{X} \to \mathbb{R}$ be measurable. Write $\bar f_n = n^{-1} \sum_{i=1}^{n} f(X_i)$ for the sample average and $E_\pi f = \int f \, d\pi$. Suppose the chain is geometrically ergodic, reversible with respect to $\pi$ (detailed balance, the source's eq. (8)), and
--
--   $$
--   E_\pi f^2 < \infty.
--   $$
--
--   Then the chain satisfies the central limit theorem for $f$: there is a single asymptotic variance $\sigma_f^2 \ge 0$ such that for every initial distribution of the chain,
--
--   $$
--   \sqrt{n}\,\bigl(\bar f_n - E_\pi f\bigr) \xrightarrow{d} N(0, \sigma_f^2) \qquad (n \to \infty).
--   $$
--
--   The Roberts–Rosenthal CLT: for reversible samplers — Metropolis–Hastings in particular — geometric ergodicity plus a second moment already gives the CLT, with no $\delta$ to spare.
--
--   **Formalization Note** "Harris ergodic" is encoded by its total-variation characterization: $\pi$ is invariant for $P$ and $\|P^n(x, \cdot) - \pi\| \to 0$ for every starting point $x$ (equivalent to the classical aperiodic, $\psi$-irreducible, positive Harris recurrent definition; the "every $x$" quantifier is exactly the Harris property). Convergence in distribution is weak convergence of laws, and $N(0, 0)$ is read as the point mass at $0$, which absorbs the source's "$\sigma_f^2 > 0$" caveat.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Corollary 4 (arXiv v2 p. 12; proved there from Theorem 7 via Theorem 2(iii)); original: G. O. Roberts & J. S. Rosenthal, Electron. Comm. Probab. 2 (1997), via Kipnis-Varadhan (1986), Corollary 1.5

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Corollary 4** (Roberts–Rosenthal 1997): a geometrically ergodic Harris chain
satisfying detailed balance, with `E_π f² < ∞`, satisfies the CLT for every initial
distribution. -/

theorem MarkovChainCLT.clt_of_geometric_reversible {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (hgeo : GeometricallyErgodic P π) (hrev : Kernel.IsReversible P π)
    (hL2 : MemLp f 2 π) :
    SatisfiesCLT P π f := by sorry
