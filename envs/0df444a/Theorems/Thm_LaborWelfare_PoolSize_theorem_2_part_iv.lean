-- Prove2me | Theorems.Thm_LaborWelfare_PoolSize_theorem_2_part_iv
-- name    : LaborWelfare.PoolSize.theorem_2_part_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:18.20672+00:00
-- url     : https://prove2.me/theorems/59e651c8-b631-465a-bd7c-f1f60deaea7c
-- title:
--   Proof of Theorem 2, Part (iv), p. OA7 — for h > 0 the wage w* decreases in N
-- statement:
--   In the base model ($h>0$), let $N\mapsto(p^*,w^*,D^*,S^*)(N)$ select an optimal outcome for every $N>\underline N$. Then the optimal wage $w^*$ is strictly decreasing in $N$ on $(\underline N,\infty)$.
--   $$N_1<N_2\ \Longrightarrow\ w^*(N_1)>w^*(N_2)\qquad(\underline N<N_1).$$
--
--   This is the wage clause of Theorem 2 for delay-sensitive customers.
-- source:
--   Benjaafar, Ding, Kong & Taylor, Labor Welfare in On-Demand Service Platforms, SSRN 3103447 (manuscript of 2020-11-13; MSOM doi:10.1287/msom.2020.0964), proof of Theorem 2, Part (iv), p. OA7

import Mathlib
import Definitions.Def_LaborWelfare_PoolSize_Setting

namespace LaborWelfare.PoolSize

open MeasureTheory Filter Topology

/-- Proof of Theorem 2, Part (iv), p. OA7: for `h > 0` the wage `w*` decreases in `N`. -/
theorem theorem_2_part_iv (M : Model) (hM : M.Std) (hh : 0 < M.h) (opt : ℝ → Outcome) (hopt : ∀ N, Nlow M < N → IsOptimal M N (opt N)) :
    StrictAntiOn (fun N => (opt N).w) (Set.Ioi (Nlow M)) := by sorry

end LaborWelfare.PoolSize
