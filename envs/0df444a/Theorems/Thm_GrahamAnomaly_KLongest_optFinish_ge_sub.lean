-- Prove2me | Theorems.Thm_GrahamAnomaly_KLongest_optFinish_ge_sub
-- name    : GrahamAnomaly.KLongest.optFinish_ge_sub
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:47:47.859435+00:00
-- url     : https://prove2.me/theorems/91c83e02-35c5-4a81-aa8b-fa9a222bb35e
-- title:
--   (15), p. 427 — optimum controls the list finishing time minus residual imbalance
-- statement:
--   Under the independent-task list rule, suppose $k<r$ and the complete list finishes after the first $k$ tasks. Write $\omega(k)$ for its finishing time, $\omega_0$ for the minimum finishing time over all assignments, and $\alpha^*$ for the longest task after the prefix. For $n>0$ processors and positive task lengths,
--
--   $$
--   \omega_0\ge\omega(k)-\frac{n-1}{n}\alpha^*.
--   $$
--
--   This is the right inequality of Graham's display (15), together with the average-load comparison shown there.
--
--   **Formalization Note** The theorem states the resulting right inequality; the average-load left inequality is a separate milestone. Prefix optimality and longest-first order are not needed for this bound.
-- source:
--   Graham, Bounds on multiprocessing timing anomalies, SIAM J. Appl. Math. 17 (1969), p. 427, proof of Theorem 3, (15), right inequality

import Mathlib
import Definitions.Def_GrahamAnomaly_KLongest_Model

namespace GrahamAnomaly.KLongest

theorem optFinish_ge_sub {r n k : ℕ} (hn : 0 < n)
    (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (L : Fin r ≃ Fin r) (σ : Fin r → Fin n)
    (hσ : IsListAssignment μ L σ) (hkr : k < r)
    (hgt : prefixFinish μ L σ k < WilliamsonShmoys.makespan μ σ) :
    WilliamsonShmoys.makespan μ σ - ((n : ℝ) - 1) / n * alphaStar μ L k ≤
      optFinish μ n := by sorry

end GrahamAnomaly.KLongest
