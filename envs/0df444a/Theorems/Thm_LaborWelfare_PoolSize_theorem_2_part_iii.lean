-- Prove2me | Theorems.Thm_LaborWelfare_PoolSize_theorem_2_part_iii
-- name    : LaborWelfare.PoolSize.theorem_2_part_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:09.691835+00:00
-- url     : https://prove2.me/theorems/541c62a2-d122-46b3-86f8-effaeab9381e
-- title:
--   Proof of Theorem 2, Part (iii), p. OA7 — LW̄ = E[1/a](w*_e)²/4 is non-monotonic in N, first increasing then decreasing
-- statement:
--   In the base model ($h>0$), let $N\mapsto(p^*,w^*,D^*,S^*)(N)$ select an optimal outcome for every $N>\underline N$. Then:
--
--   1. for every $N>\underline N$, average labor welfare at the optimum equals
--   $$\overline{LW}=\frac{E[1/a]\,(w^*_e)^2}{4};$$
--   2. there is a threshold $N_0>0$, $N_0>\underline N$, such that $\overline{LW}$ is strictly increasing in $N$ on $(\underline N,N_0)$ and strictly decreasing on $(N_0,\infty)$.
--
--   This is the headline clause of Theorem 2: with delay-sensitive customers a larger labor pool first raises and then lowers average labor welfare.
-- source:
--   Benjaafar, Ding, Kong & Taylor, Labor Welfare in On-Demand Service Platforms, SSRN 3103447 (manuscript of 2020-11-13; MSOM doi:10.1287/msom.2020.0964), proof of Theorem 2, Part (iii), p. OA7

import Mathlib
import Definitions.Def_LaborWelfare_PoolSize_Setting

namespace LaborWelfare.PoolSize

open MeasureTheory Filter Topology

/-- Proof of Theorem 2, Part (iii), p. OA7: `LW̄ = E[1/a] (w*_e)²/4`, and for `h > 0` average labor
welfare increases in `N` below a threshold above `N̲` and decreases above it. -/
theorem theorem_2_part_iii (M : Model) (hM : M.Std) (hh : 0 < M.h) (opt : ℝ → Outcome) (hopt : ∀ N, Nlow M < N → IsOptimal M N (opt N)) :
    (∀ N, Nlow M < N → avgLaborWelfare M N (opt N) = Einv M * effWage (opt N) ^ 2 / 4) ∧
      ∃ N₀, 0 < N₀ ∧ Nlow M < N₀ ∧
        StrictMonoOn (fun N => avgLaborWelfare M N (opt N)) (Set.Ioo (Nlow M) N₀) ∧
        StrictAntiOn (fun N => avgLaborWelfare M N (opt N)) (Set.Ioi N₀) := by sorry

end LaborWelfare.PoolSize
