-- Prove2me | Theorems.Thm_LaborWelfare_PoolSize_theorem_2_part_i
-- name    : LaborWelfare.PoolSize.theorem_2_part_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:59.524978+00:00
-- url     : https://prove2.me/theorems/9f77ac9d-a714-43d0-b295-b533a518a851
-- title:
--   Proof of Theorem 2, Part (i), pp. OA5–OA6 — w*_e increases in N below N̂^w_0 > N̲ and decreases above it
-- statement:
--   In the base model ($h>0$), let $N\mapsto(p^*,w^*,D^*,S^*)(N)$ select an optimal outcome for every $N>\underline N$. There is a threshold $\hat N^w_0$ with $\hat N^w_0>0$ and $\hat N^w_0>\underline N$ such that the optimal effective wage $w^*_e=w^*D^*/S^*$ is strictly increasing in $N$ on $(\underline N,\hat N^w_0)$ and strictly decreasing on $(\hat N^w_0,\infty)$:
--   $$w^*_e\ \uparrow\ \text{on}\ (\underline N,\hat N^w_0),\qquad w^*_e\ \downarrow\ \text{on}\ (\hat N^w_0,\infty).$$
--
--   This is the effective-wage clause of Theorem 2.
-- source:
--   Benjaafar, Ding, Kong & Taylor, Labor Welfare in On-Demand Service Platforms, SSRN 3103447 (manuscript of 2020-11-13; MSOM doi:10.1287/msom.2020.0964), proof of Theorem 2, Part (i), pp. OA5–OA6 (Step 4, p. OA6)

import Mathlib
import Definitions.Def_LaborWelfare_PoolSize_Setting

namespace LaborWelfare.PoolSize

open MeasureTheory Filter Topology

/-- Proof of Theorem 2, Part (i), pp. OA5–OA6: for `h > 0` the effective wage `w*_e` increases in `N`
on `(N̲, N̂^w_0)` and decreases on `(N̂^w_0, ∞)`, for some `N̂^w_0 > N̲`, `N̂^w_0 > 0`. -/
theorem theorem_2_part_i (M : Model) (hM : M.Std) (hh : 0 < M.h) (opt : ℝ → Outcome) (hopt : ∀ N, Nlow M < N → IsOptimal M N (opt N)) :
    ∃ N₀, 0 < N₀ ∧ Nlow M < N₀ ∧
      StrictMonoOn (fun N => effWage (opt N)) (Set.Ioo (Nlow M) N₀) ∧
      StrictAntiOn (fun N => effWage (opt N)) (Set.Ioi N₀) := by sorry

end LaborWelfare.PoolSize
