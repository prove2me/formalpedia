-- Prove2me | Theorems.Thm_KellyReversibility_Allocation_optimal_capacity_allocation
-- name    : KellyReversibility.Allocation.optimal_capacity_allocation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:08:21.715493+00:00
-- url     : https://prove2.me/theorems/3d43bc0f-26cb-437f-90c4-1299cdb046fb
-- title:
--   Theorem 4.1 — optimal capacity allocation φ_j = a_j + √(a_j f_j)/∑√(a_k f_k) · (F − ∑ a_k f_k)/f_j
-- statement:
--   A communication network has $J \ge 1$ channels. Channel $j$ has average arrival rate $a_j > 0$ and, if given capacity $\phi_j > a_j$, holds on average $a_j/(\phi_j - a_j)$ customers. Capacity on channel $j$ costs $f_j > 0$ per unit, and the capacities must satisfy the cost constraint (4.2)
--   $$\sum_j f_j\phi_j = F,$$
--   where the budget satisfies $F > \sum_k a_k f_k$. Among all capacity vectors $\phi$ with $\phi_j > a_j$ for every $j$ and satisfying (4.2), the mean number of customers in the network
--   $$\sum_j \frac{a_j}{\phi_j - a_j}$$
--   is minimized by the allocation
--   $$\phi^*_j = a_j + \frac{\sqrt{a_j f_j}}{\sum_k \sqrt{a_k f_k}}\cdot\frac{F - \sum_k a_k f_k}{f_j}.$$
--   Precisely: $\phi^*$ is feasible, it attains the minimum over the feasible set, and every other feasible $\phi$ gives a strictly larger mean number of customers.
--
--   Each channel first receives the capacity $a_j$ needed to carry its traffic; the excess budget $F - \sum_k a_k f_k$ is then shared in proportion to $\sqrt{a_j f_j}$. As the book observes, minimizing the mean number of customers in the network is equivalent to minimizing the average time a customer spends in it.
--
--   **Formalization Note** The book leaves implicit that $a_j > 0$, $f_j > 0$, $J \ge 1$ and $F > \sum_k a_k f_k$; without the last the feasible set is empty. The stability condition $\phi_j > a_j$ is part of the feasible set. The uniqueness clause (strict inequality for every other feasible point) slightly strengthens the book's "The optimal allocation is"; it holds because the objective is strictly convex.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 97, Theorem 4.1 (with the cost constraint (4.2) and the objective of its proof)

import Mathlib
import Definitions.Def_KellyReversibility_Allocation_CapacityAllocation

namespace KellyReversibility.Allocation

theorem optimal_capacity_allocation {J : ℕ} (hJ : 0 < J) (a f : Fin J → ℝ) (F : ℝ)
    (ha : ∀ j, 0 < a j) (hf : ∀ j, 0 < f j) (hF : ∑ k, a k * f k < F) :
    optimalAllocation a f F ∈ FeasibleCapacities a f F ∧
      IsMinOn (meanNumberInNetwork a) (FeasibleCapacities a f F) (optimalAllocation a f F) ∧
      ∀ φ ∈ FeasibleCapacities a f F, φ ≠ optimalAllocation a f F →
        meanNumberInNetwork a (optimalAllocation a f F) < meanNumberInNetwork a φ := by sorry

end KellyReversibility.Allocation
