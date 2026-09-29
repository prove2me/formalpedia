-- Prove2me | Theorems.Thm_MarkovChainCLT_alpha_mixing_le_tv_rate
-- name    : MarkovChainCLT.alpha_mixing_le_tv_rate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:38:01.354379+00:00
-- url     : https://prove2.me/theorems/a80ec800-1cb3-4132-997a-395634a20a3d
-- title:
--   $\alpha(n) \le \gamma(n)\, E_\pi M$ from a total-variation rate (Jones Thm 2(ii))
-- statement:
--   Let $X$ be a Markov chain with transition kernel $P$, Harris ergodic with invariant probability $\pi$, and suppose the total-variation rate bound $\|P^n(x, \cdot) - \pi\| \le M(x)\, \gamma(n)$ holds for all $x$ and all $n \ge 1$, where $M \ge 0$ is integrable with respect to $\pi$ and $\gamma \ge 0$. Then the strong mixing coefficients of the stationary chain satisfy
--
--   $$
--   \alpha(n) \;\le\; \gamma(n) \int M \, d\pi \qquad (n \ge 1).
--   $$
--
--   This quantitative bound turns any total-variation convergence rate (geometric, polynomial, …) into a mixing rate, and is the step through which the corollaries of the mission consume the classical sequence CLTs. The source records the consequence $\alpha(n) = O(\gamma(n))$; the sharp inequality stated here is what its derivation gives.
--
--   **Formalization Note** "Harris ergodic" is encoded by its total-variation characterization: $\pi$ is invariant for $P$ and $\|P^n(x, \cdot) - \pi\| \to 0$ for every starting point $x$ (equivalent to the classical aperiodic, $\psi$-irreducible, positive Harris recurrent definition; the "every $x$" quantifier is exactly the Harris property). Convergence in distribution is weak convergence of laws, and $N(0, 0)$ is read as the point mass at $0$, which absorbs the source's "$\sigma_f^2 > 0$" caveat.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorem 2, part 2 (arXiv v2 p. 8; Section 3 derivation via the coupling inequality, eq. (7))

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Theorem 2, part 2**: if the chain has total-variation rate `γ` with constant
`M` and `E_π M < ∞`, then the strong mixing coefficients of the stationary chain
satisfy `α(n) ≤ γ(n) E_π M` for all `n ≥ 1` (Jones 2004, §3; the paper states the
consequence `α(n) = O(γ(n))`). -/

theorem MarkovChainCLT.alpha_mixing_le_tv_rate {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π)
    (M : X → ℝ) (hM0 : ∀ x, 0 ≤ M x) (hM : Integrable M π)
    (γ : ℕ → ℝ) (hγ0 : ∀ n, 0 ≤ γ n) (hrate : ErgodicWithRate P π M γ) :
    ∀ n : ℕ, 1 ≤ n →
      alphaMixingCoef (chainMeasure P π) (fun i ω => ω i) n ≤ γ n * ∫ x, M x ∂π := by sorry
