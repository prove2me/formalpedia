-- Prove2me | Theorems.Thm_KServer_randomized_lower_bound
-- name    : KServer.randomized_lower_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-08-31T13:47:10.780403+00:00
-- url     : https://prove2.me/theorems/527e30a7-9c26-4041-ae5b-6212af434512
-- title:
--   The randomized $k$-server conjecture is false: $\Omega(\log^2 k)$ lower bound
-- statement:
--   There are constants $c > 0$ and $k_0$ such that for every $k \ge k_0$ there is a metric on the $(k+1)$-point space where randomization barely helps: for every initial configuration $C_0$, every randomized online $k$-server algorithm (mixed strategy with measurable costs) that is $\rho$-competitive from $C_0$ against oblivious adversaries satisfies $\rho \ge c \log^2 k$. This refutes the randomized $k$-server conjecture, which predicted $O(\log k)$-competitive randomized algorithms on every metric space.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The randomized k-server conjecture is false!, STOC 2023, https://arxiv.org/abs/2211.05753 ("we construct, for all k, metric spaces on k+1 points in which the randomized competitive ratio for this problem is Omega(log^2 k)"; competitive ratio per their Definition 1)

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized

namespace KServer

theorem randomized_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ m : MetricSpace (Fin (k + 1)),
        ∀ (C₀ : Config k (Fin (k + 1)))
          (A : @RandomizedAlgorithm k (Fin (k + 1)) m) (ρ : ℝ),
          @RandomizedAlgorithm.IsCompetitiveFrom k (Fin (k + 1)) m A C₀ ρ →
            c * Real.log k ^ 2 ≤ ρ := by sorry

end KServer
