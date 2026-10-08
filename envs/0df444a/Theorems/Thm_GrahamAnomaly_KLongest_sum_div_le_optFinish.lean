-- Prove2me | Theorems.Thm_GrahamAnomaly_KLongest_sum_div_le_optFinish
-- name    : GrahamAnomaly.KLongest.sum_div_le_optFinish
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:47:06.250006+00:00
-- url     : https://prove2.me/theorems/a6116995-b28f-41bf-9068-ddd1b75ec3e0
-- title:
--   (15), p. 427 — optimal finishing time exceeds average total work
-- statement:
--   Let $n$ be a positive number of identical processors and let $\mu_j>0$ be the lengths of finitely many tasks. If $\omega_0$ is the least finishing time over all assignments of these tasks, then
--
--   $$
--   \frac{1}{n}\sum_j\mu_j\le\omega_0.
--   $$
--
--   This is the average-load lower bound in the left half of Graham's display (15). It applies to every assignment, including an optimal one.
--
--   **Formalization Note** An empty task set is allowed here, in which case both sides are zero. The processor set is nonempty because $n>0$.
-- source:
--   Graham, Bounds on multiprocessing timing anomalies, SIAM J. Appl. Math. 17 (1969), p. 427, (15), left inequality

import Mathlib
import Definitions.Def_GrahamAnomaly_KLongest_Model

namespace GrahamAnomaly.KLongest

theorem sum_div_le_optFinish {r n : ℕ} (hn : 0 < n) (μ : Fin r → ℝ)
    (hμ : ∀ j, 0 < μ j) :
    (1 / (n : ℝ)) * ∑ j, μ j ≤ optFinish μ n := by sorry

end GrahamAnomaly.KLongest
