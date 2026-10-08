-- Prove2me | Theorems.Thm_GrahamAnomaly_KLongest_optFinish_ge_alphaStar
-- name    : GrahamAnomaly.KLongest.optFinish_ge_alphaStar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:47:51.951123+00:00
-- url     : https://prove2.me/theorems/44a094e7-70a2-49e9-9e90-c62f63beb5bc
-- title:
--   (16), p. 427 — pigeonhole lower bound from the long tasks
-- statement:
--   Let $n>0$ processors and $r$ positive-length tasks be given. The first $k<r$ list positions hold $k$ of the longest tasks, and $\alpha^*$ is the longest length among the remaining tasks. If $\omega_0$ is the minimum finishing time among assignments, then
--
--   $$
--   \omega_0\ge\bigl(1+\lfloor k/n\rfloor\bigr)\alpha^*.
--   $$
--
--   This is Graham's display (16): there are at least $k+1$ tasks of length at least $\alpha^*$, so some processor must receive at least $1+\lfloor k/n\rfloor$ of them.
--
--   **Formalization Note** The list order is constrained only by the longest-first condition; no particular list assignment is needed. The natural-number quotient $k/n$ is the paper's greatest-integer function.
-- source:
--   Graham, Bounds on multiprocessing timing anomalies, SIAM J. Appl. Math. 17 (1969), p. 427, proof of Theorem 3, (16)

import Mathlib
import Definitions.Def_GrahamAnomaly_KLongest_Model

namespace GrahamAnomaly.KLongest

theorem optFinish_ge_alphaStar {r n k : ℕ} (hn : 0 < n) (hk : k ≤ r)
    (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (L : Fin r ≃ Fin r)
    (hlong : ∀ i j, (L.symm i : ℕ) < k → k ≤ (L.symm j : ℕ) → μ j ≤ μ i)
    (hkr : k < r) :
    (1 + ((k / n : ℕ) : ℝ)) * alphaStar μ L k ≤ optFinish μ n := by sorry

end GrahamAnomaly.KLongest
