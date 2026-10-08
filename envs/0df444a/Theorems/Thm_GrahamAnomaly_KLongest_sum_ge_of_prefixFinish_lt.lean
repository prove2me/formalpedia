-- Prove2me | Theorems.Thm_GrahamAnomaly_KLongest_sum_ge_of_prefixFinish_lt
-- name    : GrahamAnomaly.KLongest.sum_ge_of_prefixFinish_lt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:47:39.338706+00:00
-- url     : https://prove2.me/theorems/b9417a38-0832-4f17-99c8-13eee0d5919f
-- title:
--   (14), p. 427 — volume bound from the longest remaining task
-- statement:
--   Let $n>0$ processors execute positive-length tasks by the least-loaded list rule. Suppose some task remains after the first $k$ positions, and the full finishing time $\omega(k)$ exceeds the prefix finishing time $\omega_k$. Let $\alpha^*$ be the largest length among tasks after position $k$. Then
--
--   $$
--   \sum_j\mu_j\ge n\bigl(\omega(k)-\alpha^*\bigr)+\alpha^*.
--   $$
--
--   This is Graham's display (14), which measures the total task volume needed for a run with that finishing time.
--
--   **Formalization Note** This statement uses only the list rule, positive lengths, $k<r$, and the strict comparison $\omega_k<\omega(k)$. The later longest-prefix and prefix-optimality assumptions are not needed for (14).
-- source:
--   Graham, Bounds on multiprocessing timing anomalies, SIAM J. Appl. Math. 17 (1969), p. 427, proof of Theorem 3, (14)

import Mathlib
import Definitions.Def_GrahamAnomaly_KLongest_Model

namespace GrahamAnomaly.KLongest

theorem sum_ge_of_prefixFinish_lt {r n k : ℕ} (hn : 0 < n)
    (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (L : Fin r ≃ Fin r) (σ : Fin r → Fin n)
    (hσ : IsListAssignment μ L σ) (hkr : k < r)
    (hgt : prefixFinish μ L σ k < WilliamsonShmoys.makespan μ σ) :
    (n : ℝ) * (WilliamsonShmoys.makespan μ σ - alphaStar μ L k) +
      alphaStar μ L k ≤ ∑ j, μ j := by sorry

end GrahamAnomaly.KLongest
