-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_geometric_or_polynomial
-- name    : MarkovChainCLT.clt_of_geometric_or_polynomial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:40:29.111366+00:00
-- url     : https://prove2.me/theorems/48b55b4d-6f42-438d-92f7-c0645a747047
-- title:
--   Chan–Geyer and polynomial-ergodicity CLTs (Jones Cor 2)
-- statement:
--   Let $X = \{X_n\}_{n \ge 0}$ be a Markov chain with transition kernel $P$ on a state space $\mathsf{X}$, Harris ergodic with invariant probability distribution $\pi$, and let $f : \mathsf{X} \to \mathbb{R}$ be measurable. Write $\bar f_n = n^{-1} \sum_{i=1}^{n} f(X_i)$ for the sample average and $E_\pi f = \int f \, d\pi$. Assume one of the following three conditions: (1) the chain is geometrically ergodic and $E_\pi |f|^{2+\delta} < \infty$ for some $\delta > 0$; (2) the chain is polynomially ergodic of order $m$ with $E_\pi M < \infty$ for the rate constant $M$, and $E_\pi |f|^{2+\delta} < \infty$ for some $\delta > 0$ with $m\delta > 2 + \delta$; (3) the chain is polynomially ergodic of order $m > 1$ with $E_\pi M < \infty$, and $|f| < B$ $\pi$-almost surely for some $B$.
--
--   Then the chain satisfies the central limit theorem for $f$: there is a single asymptotic variance $\sigma_f^2 \ge 0$ such that for every initial distribution of the chain,
--
--   $$
--   \sqrt{n}\,\bigl(\bar f_n - E_\pi f\bigr) \xrightarrow{d} N(0, \sigma_f^2) \qquad (n \to \infty).
--   $$
--
--   Case (1) is the Chan–Geyer CLT, the most frequently cited sufficient condition in the MCMC literature; cases (2)–(3) are its polynomial analogues.
--
--   **Formalization Note** "Harris ergodic" is encoded by its total-variation characterization: $\pi$ is invariant for $P$ and $\|P^n(x, \cdot) - \pi\| \to 0$ for every starting point $x$ (equivalent to the classical aperiodic, $\psi$-irreducible, positive Harris recurrent definition; the "every $x$" quantifier is exactly the Harris property). Convergence in distribution is weak convergence of laws, and $N(0, 0)$ is read as the point mass at $0$, which absorbs the source's "$\sigma_f^2 > 0$" caveat.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Corollary 2 (arXiv v2 p. 10); case 1: K. S. Chan & C. J. Geyer, Ann. Statist. 22 (1994), discussion of Tierney

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Corollary 2** (case 1: Chan–Geyer 1994): a Harris ergodic chain satisfying one
of: (1) geometric ergodicity with `E_π |f|^{2+δ} < ∞` for some `δ > 0`;
(2) polynomial ergodicity of order `m` with integrable constant and
`E_π |f|^{2+δ} < ∞` with `mδ > 2+δ`; (3) polynomial ergodicity of order `m > 1`
with integrable constant and `f` bounded `π`-a.s. — satisfies the CLT for every
initial distribution. -/

theorem MarkovChainCLT.clt_of_geometric_or_polynomial {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (hcase :
      (GeometricallyErgodic P π ∧
        ∃ δ : ℝ, 0 < δ ∧ Integrable (fun x => |f x| ^ (2 + δ)) π) ∨
      (∃ m δ : ℝ, 0 < δ ∧ 2 + δ < m * δ ∧ PolynomiallyErgodicL1 P π m ∧
        Integrable (fun x => |f x| ^ (2 + δ)) π) ∨
      (∃ m : ℝ, 1 < m ∧ PolynomiallyErgodicL1 P π m ∧
        ∃ B : ℝ, ∀ᵐ x ∂π, |f x| < B)) :
    SatisfiesCLT P π f := by sorry
