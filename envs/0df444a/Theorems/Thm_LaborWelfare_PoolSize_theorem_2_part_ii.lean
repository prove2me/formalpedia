-- Prove2me | Theorems.Thm_LaborWelfare_PoolSize_theorem_2_part_ii
-- name    : LaborWelfare.PoolSize.theorem_2_part_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:01.966469+00:00
-- url     : https://prove2.me/theorems/f6ef3ad7-fcb4-4bc6-8948-3393a5eeccfd
-- title:
--   Proof of Theorem 2, Part (ii), pp. OA6–OA7 — ρ* = D*/S* increases in N below N̂^ρ_0 > N̲ and decreases above it
-- statement:
--   In the base model ($h>0$), let $N\mapsto(p^*,w^*,D^*,S^*)(N)$ select an optimal outcome for every $N>\underline N$. There is a threshold $\hat N^\rho_0$ with $\hat N^\rho_0>0$ and $\hat N^\rho_0>\underline N$ such that agent utilization $\rho^*=D^*/S^*$ is strictly increasing in $N$ on $(\underline N,\hat N^\rho_0)$ and strictly decreasing on $(\hat N^\rho_0,\infty)$:
--   $$\rho^*\ \uparrow\ \text{on}\ (\underline N,\hat N^\rho_0),\qquad \rho^*\ \downarrow\ \text{on}\ (\hat N^\rho_0,\infty).$$
--
--   This is the utilization clause of Theorem 2.
-- source:
--   Benjaafar, Ding, Kong & Taylor, Labor Welfare in On-Demand Service Platforms, SSRN 3103447 (manuscript of 2020-11-13; MSOM doi:10.1287/msom.2020.0964), proof of Theorem 2, Part (ii), pp. OA6–OA7 (Step 3, p. OA7)

import Mathlib
import Definitions.Def_LaborWelfare_PoolSize_Setting

namespace LaborWelfare.PoolSize

open MeasureTheory Filter Topology

/-- Proof of Theorem 2, Part (ii), pp. OA6–OA7: for `h > 0` the utilization `ρ* = D*/S*` increases in
`N` on `(N̲, N̂^ρ_0)` and decreases on `(N̂^ρ_0, ∞)`, for some `N̂^ρ_0 > N̲`, `N̂^ρ_0 > 0`. -/
theorem theorem_2_part_ii (M : Model) (hM : M.Std) (hh : 0 < M.h) (opt : ℝ → Outcome) (hopt : ∀ N, Nlow M < N → IsOptimal M N (opt N)) :
    ∃ N₀, 0 < N₀ ∧ Nlow M < N₀ ∧
      StrictMonoOn (fun N => util (opt N)) (Set.Ioo (Nlow M) N₀) ∧
      StrictAntiOn (fun N => util (opt N)) (Set.Ioi N₀) := by sorry

end LaborWelfare.PoolSize
