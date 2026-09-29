-- Prove2me | Theorems.Thm_KServer_work_function_upper_bound
-- name    : KServer.work_function_upper_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:11:54.645251+00:00
-- url     : https://prove2.me/theorems/2f768738-f2ff-4ed6-9a7f-2401840accaf
-- title:
--   Koutsoupias--Papadimitriou: a $(2k-1)$-competitive algorithm on every metric space
-- statement:
--   (Koutsoupias--Papadimitriou, 1995.) On every metric space and from every initial configuration there is a $(2k-1)$-competitive deterministic online $k$-server algorithm. The witness in the source is the **Work Function Algorithm**, which serves each request by the server minimizing the sum of movement cost and the offline work function value at the resulting configuration. This is the strongest general upper bound known — unimproved since 1995 — and the deepest single result in the area.
-- source:
--   Koutsoupias--Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995), Theorem 1, https://doi.org/10.1145/210118.210128

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem work_function_upper_bound (k : ℕ) (hk : 1 ≤ k) (M : Type)
    [MetricSpace M] (C₀ : Config k M) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧
      IsCompetitive A (2 * (k : ℝ) - 1) := by sorry

end KServer
