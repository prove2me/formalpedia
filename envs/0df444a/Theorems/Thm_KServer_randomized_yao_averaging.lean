-- Prove2me | Theorems.Thm_KServer_randomized_yao_averaging
-- name    : KServer.randomized_yao_averaging
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T08:25:36.093143+00:00
-- url     : https://prove2.me/theorems/bfeb4832-02cf-415a-941f-1460648e1ae2
-- title:
--   Yao averaging: a competitive mixed strategy contains a good deterministic algorithm
-- statement:
--   Let $\widetilde{\mathcal{A}}$ be a randomized online $k$-server algorithm (a mixed strategy: a probability measure over deterministic algorithms) that is $\rho$-competitive from the configuration $C_0$ against oblivious adversaries, with $\rho \ge 0$. Then there is a constant $a \ge 0$ such that for every finitely supported probability distribution $(p_1, \sigma_1), \dots, (p_m, \sigma_m)$ over request sequences and every $\varepsilon > 0$, some deterministic algorithm $\mathcal{A}$ in the support of $\widetilde{\mathcal{A}}$ starts at $C_0$ and satisfies
--
--   $$\sum_{j=1}^m p_j \, c_{\mathcal{A}}(\sigma_j) \;\le\; \rho \sum_{j=1}^m p_j \, c_{\mathrm{OPT}}(\sigma_j) \;+\; a \;+\; \varepsilon.$$
--
--   ## Role
--
--   This is the easy (averaging) direction of Yao's minimax principle, in the form needed for randomized lower bounds: to show that every $\rho$-competitive randomized algorithm has $\rho \ge L$, it suffices to exhibit request distributions against which **every deterministic algorithm** pays at least $L$ times the expected offline cost plus an arbitrarily large constant. It is the first pillar of the Bubeck–Coester–Rabani refutation of the randomized $k$-server conjecture (STOC 2023), which constructs such distributions on $(k+1)$-point spaces forcing $L = \Omega(\log^2 k)$.
--
--   The proof is an exercise in the linearity and monotonicity of the lower Lebesgue integral: the expected average cost of the randomized algorithm is the average of its expected costs (Fubini for finite sums, using the measurability field of the mixed strategy), each bounded by $\rho\, c_{\mathrm{OPT}}(\sigma_j) + a$; if every outcome exceeded the average bound by $\varepsilon$, integrating the pointwise bound over the probability measure would contradict it.
--
--   ## Formalization note
--
--   Expected costs are lower Lebesgue integrals valued in `ENNReal`; the constant is normalized to $\max(a,0)$ so that the comparison of `ENNReal.ofReal`s can be reflected back to the reals, and the $\varepsilon$ of slack absorbs the fact that a lower integral bound only yields pointwise bounds up to any positive margin.
-- source:
--   A. C.-C. Yao, 'Probabilistic computations: toward a unified measure of complexity', FOCS 1977 (the averaging direction); as used in S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Section 2.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized

namespace KServer

theorem randomized_yao_averaging (k : ℕ) (M : Type*) [MetricSpace M]
    (A : RandomizedAlgorithm k M) (C₀ : Config k M) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hA : A.IsCompetitiveFrom C₀ ρ) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ (m : ℕ) (p : Fin m → ℝ), (∀ j, 0 ≤ p j) → (∑ j, p j) = 1 →
      ∀ (σ : Fin m → List M) (ε : ℝ), 0 < ε →
        ∃ i : A.ι, (A.alg i).conf [] = C₀ ∧
          ∑ j, p j * (A.alg i).cost (σ j)
            ≤ ρ * (∑ j, p j * offlineCost C₀ (σ j)) + a + ε := by sorry

end KServer
