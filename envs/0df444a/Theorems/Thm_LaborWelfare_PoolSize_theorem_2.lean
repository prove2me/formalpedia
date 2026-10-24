-- Prove2me | Theorems.Thm_LaborWelfare_PoolSize_theorem_2
-- name    : LaborWelfare.PoolSize.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:12.995915+00:00
-- url     : https://prove2.me/theorems/079115a1-da1e-41ae-956b-abd306073b59
-- title:
--   Theorem 2, p. 11 — h = 0: w*, w*_e, LW̄ decrease in N; h > 0: w* decreases, D*/S*, w*_e, LW̄ first increase then decrease in N
-- statement:
--   Let the standing assumptions of §3 hold, and let $N\mapsto(p^*,w^*,D^*,S^*)(N)$ select, for every labor pool size $N>\underline N$, an optimal outcome of the platform's problem (7): the price $p^*\ge0$ and wage $w^*\ge0$ maximize the profit $(p-w)D$ subject to the market equilibrium (2)–(4).
--
--   1. **Delay-insensitive customers ($h=0$).** The wage $w^*$, the effective wage $w^*_e=w^*D^*/S^*$ and average labor welfare $\overline{LW}$ are strictly decreasing in $N$ on $(0,\infty)$.
--   2. **Delay-sensitive customers ($h>0$).** The wage $w^*$ is strictly decreasing in $N$ on $(\underline N,\infty)$. Agent utilization $D^*/S^*$, the effective wage $w^*_e$ and $\overline{LW}$ are each non-monotonic: for each of these three quantities $Q$ there is a threshold $N_0$ with $N_0>0$ and $N_0>\underline N$ such that
--   $$Q\ \text{is strictly increasing on}\ (\underline N,N_0)\quad\text{and strictly decreasing on}\ (N_0,\infty).$$
--
--   In a standard labor market a larger pool lowers wages and welfare; when customers are sensitive to delay, a larger pool first raises average labor welfare, because added supply reduces delay and stimulates demand, and only beyond a threshold does the usual cost effect dominate.
--
--   **Formalization Note** "Increasing" and "decreasing" are strict (p. 11). For $h=0$, $\underline N=0$. The three thresholds are separate, as the page says "for each performance measure". The optimum is a selection constrained to be optimal for every $N>\underline N$; it exists and is unique there (Lemma 1; p. 10 for $h=0$), so it is the paper's optimum.
-- source:
--   Benjaafar, Ding, Kong & Taylor, Labor Welfare in On-Demand Service Platforms, SSRN 3103447 (manuscript of 2020-11-13; MSOM doi:10.1287/msom.2020.0964), Theorem 2, p. 11 (proof pp. OA4–OA7)

import Mathlib
import Definitions.Def_LaborWelfare_PoolSize_Setting

namespace LaborWelfare.PoolSize

open MeasureTheory Filter Topology

/-- Theorem 2, p. 11. For `h = 0`, `w*`, `w*_e` and `LW̄` decrease in `N`. For `h > 0`, `w*` decreases in
`N`, while `D*/S*`, `w*_e` and `LW̄` each increase below a strictly positive threshold on `N` and decrease
above it. -/
theorem theorem_2 (M : Model) (hM : M.Std) (opt : ℝ → Outcome) (hopt : ∀ N, Nlow M < N → IsOptimal M N (opt N)) :
    (M.h = 0 →
        StrictAntiOn (fun N => (opt N).w) (Set.Ioi 0) ∧
        StrictAntiOn (fun N => effWage (opt N)) (Set.Ioi 0) ∧
        StrictAntiOn (fun N => avgLaborWelfare M N (opt N)) (Set.Ioi 0)) ∧
      (0 < M.h →
        StrictAntiOn (fun N => (opt N).w) (Set.Ioi (Nlow M)) ∧
        (∃ N₀, 0 < N₀ ∧ Nlow M < N₀ ∧
          StrictMonoOn (fun N => util (opt N)) (Set.Ioo (Nlow M) N₀) ∧
          StrictAntiOn (fun N => util (opt N)) (Set.Ioi N₀)) ∧
        (∃ N₀, 0 < N₀ ∧ Nlow M < N₀ ∧
          StrictMonoOn (fun N => effWage (opt N)) (Set.Ioo (Nlow M) N₀) ∧
          StrictAntiOn (fun N => effWage (opt N)) (Set.Ioi N₀)) ∧
        (∃ N₀, 0 < N₀ ∧ Nlow M < N₀ ∧
          StrictMonoOn (fun N => avgLaborWelfare M N (opt N)) (Set.Ioo (Nlow M) N₀) ∧
          StrictAntiOn (fun N => avgLaborWelfare M N (opt N)) (Set.Ioi N₀))) := by sorry

end LaborWelfare.PoolSize
