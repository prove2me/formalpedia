-- Prove2me | Theorems.Thm_MarkovChainCLT_strongly_mixing_of_harris
-- name    : MarkovChainCLT.strongly_mixing_of_harris
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:37:43.302967+00:00
-- url     : https://prove2.me/theorems/479d8db4-ac50-43b0-b4b4-a1a607c03834
-- title:
--   Harris ergodic chains are strongly mixing: $\alpha(n) \to 0$ (Jones Thm 2(i))
-- statement:
--   Let $X$ be a Markov chain with transition kernel $P$, Harris ergodic with invariant probability $\pi$, and consider its stationary version (initial distribution $\pi$). Then the chain is strongly mixing:
--
--   $$
--   \alpha(n) \;\longrightarrow\; 0 \qquad (n \to \infty),
--   $$
--
--   where $\alpha(n)$ is the strong mixing coefficient of the coordinate process.
--
--   This is the bridge that makes the entire classical theory of CLTs for mixing sequences applicable to Markov chain Monte Carlo.
--
--   **Formalization Note** "Harris ergodic" is encoded by its total-variation characterization: $\pi$ is invariant for $P$ and $\|P^n(x, \cdot) - \pi\| \to 0$ for every starting point $x$ (equivalent to the classical aperiodic, $\psi$-irreducible, positive Harris recurrent definition; the "every $x$" quantifier is exactly the Harris property). Convergence in distribution is weak convergence of laws, and $N(0, 0)$ is read as the point mass at $0$, which absorbs the source's "$\sigma_f^2 > 0$" caveat. The $\sigma$-algebra of the state space is additionally assumed countably generated, the standard general-state-space setting of Meyn and Tweedie.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorem 2, part 1 (arXiv v2 p. 8; proved in Section 3 via the coupling inequality, eq. (7))

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Theorem 2, part 1**: the stationary version of a Harris ergodic chain is
strongly mixing: `α(n) → 0`. -/

theorem MarkovChainCLT.strongly_mixing_of_harris {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) :
    Tendsto (fun n => alphaMixingCoef (chainMeasure P π) (fun i ω => ω i) n)
      atTop (𝓝 0) := by sorry
