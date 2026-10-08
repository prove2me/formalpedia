-- Prove2me | Theorems.Thm_GrahamAnomaly_KLongest_theorem_3
-- name    : GrahamAnomaly.KLongest.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:48:52.262693+00:00
-- url     : https://prove2.me/theorems/63478180-7db6-453b-939a-4dd4a12eeedf
-- title:
--   Theorem 3, p. 427 — k-longest-first makespan ratio
-- statement:
--   Let $r>0$ independent tasks have positive lengths $\mu_j$, and let $n>0$ identical processors execute them. Choose $0\le k\le r$ tasks of greatest length as the first $k$ positions of a priority list $L$, in an order whose list assignment has the smallest possible prefix finishing time $\omega_k$. Append the other tasks in any order, assigning each next task to a least-loaded processor. If $\omega(k)$ is the resulting finishing time and $\omega_0$ is the minimum finishing time for all tasks, then
--
--   $$
--   \frac{\omega(k)}{\omega_0}\le 1+\frac{1-1/n}{1+\lfloor k/n\rfloor}.
--   $$
--
--   This is the approximation guarantee of Graham's Theorem 3. Its best-possible example for $n\mid k$ is a separate companion item.
--
--   **Formalization Note** The first $k$ tasks must be longest, and their assignment must be optimal for those tasks alone; neither condition is replaced by an assumption of the intermediate inequalities. The integer quotient is the floor. Assignments are equivalent to the paper's lists for the optimum in this independent-task setting, and least-load ties are unrestricted.
-- source:
--   Graham, Bounds on multiprocessing timing anomalies, SIAM J. Appl. Math. 17 (1969), p. 427, Theorem 3

import Mathlib
import Definitions.Def_GrahamAnomaly_KLongest_Model

namespace GrahamAnomaly.KLongest

theorem theorem_3 {r n k : ℕ} (hr : 0 < r) (hn : 0 < n) (hk : k ≤ r)
    (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (L : Fin r ≃ Fin r) (σ : Fin r → Fin n)
    (hlong : ∀ i j, (L.symm i : ℕ) < k → k ≤ (L.symm j : ℕ) → μ j ≤ μ i)
    (hσ : IsListAssignment μ L σ)
    (hopt : ∀ τ : Fin r → Fin n, prefixFinish μ L σ k ≤ prefixFinish μ L τ k) :
    WilliamsonShmoys.makespan μ σ / optFinish μ n ≤
      1 + (1 - 1 / (n : ℝ)) / (1 + ((k / n : ℕ) : ℝ)) := by sorry

end GrahamAnomaly.KLongest
