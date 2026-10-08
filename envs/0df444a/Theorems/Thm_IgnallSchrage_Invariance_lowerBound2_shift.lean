-- Prove2me | Theorems.Thm_IgnallSchrage_Invariance_lowerBound2_shift
-- name    : IgnallSchrage.Invariance.lowerBound2_shift
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:19.824992+00:00
-- url     : https://prove2.me/theorems/0924ba1f-5947-4678-bae2-9b7910c12b9b
-- title:
--   p. 411 — on two machines, adding $G$ raises $\hat T_r,\hat S_r$, $\sum_{J_r}d_i$ and $LB(J_r)$ by explicit constants
-- statement:
--   Consider $n$ jobs on two machines with nonnegative processing times, and let $G>0$. Let $J_r$ be a node, a sequence of $r$ distinct jobs, with $1\le r\le n-1$. Add $G$ to every processing time. Then
--
--   1. $\hat T_r$ and $\hat S_r$ each increase by $G\big[r(n-r)+\tfrac12(n-r)(n-r+1)+(n-r)\big]$;
--   2. $\sum_{i\in J_r}d_i$ increases by $\tfrac12\,G\,r(r+3)$;
--   3. the lower bound $LB(J_r)=\sum_{i\in J_r}d_i+\max(\hat T_r,\hat S_r)$ increases by their sum,
--   $$
--   \tfrac12\,G\,r(r+3)+G\big[r(n-r)+\tfrac12(n-r)(n-r+1)+(n-r)\big]=\tfrac12\,G\,n(n+3).
--   $$
--
--   All nodes the procedure ranks therefore move by the same constant $\tfrac12Gn(n+3)$, the same constant by which the objective of every full sequence moves.
--
--   **Formalization Note** The page prints "$\sum_{J_r} d_i$ is increased by $\tfrac12 r(r+3)$", without the factor $G$. This is a slip, corrected here. The root $r=0$ is excluded: it has no last job $k$, and the procedure never ranks it. Nonnegative processing times are assumed, as for the completion-time shift.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 411, Appendix, proof of the THEOREM (T̂_r, Ŝ_r, Σ_{J_r} d_i and LB(J_r) increased)

import Mathlib
import Definitions.Def_IgnallSchrage_Invariance_TwoMachine

namespace IgnallSchrage.Invariance

/-- p. 411: on two machines, adding `G` to all processing times (all nonnegative) raises, at every node `J_r`
with `1 ≤ r ≤ n - 1`, both `T̂_r` and `Ŝ_r` by `G [r(n-r) + ½(n-r)(n-r+1) + (n-r)]`,
`Σ_{J_r} d_i` by `½ G r (r + 3)` (the page prints `½ r (r + 3)`, without `G`), and
`LB(J_r)` by `½ G n (n + 3)`. -/
theorem lowerBound2_shift {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (G : ℝ) (hG : 0 < G)
    (J : List (Fin n)) (hJ : J.Nodup) (hr1 : 1 ≤ J.length) (hrn : J.length + 1 ≤ n) :
    That (fun i => a i + G) (fun i => b i + G) J =
      That a b J + G * ((J.length : ℝ) * ((n : ℝ) - J.length) +
        ((n : ℝ) - J.length) * ((n : ℝ) - J.length + 1) / 2 + ((n : ℝ) - J.length)) ∧
    Shat (fun i => a i + G) (fun i => b i + G) J =
      Shat a b J + G * ((J.length : ℝ) * ((n : ℝ) - J.length) +
        ((n : ℝ) - J.length) * ((n : ℝ) - J.length + 1) / 2 + ((n : ℝ) - J.length)) ∧
    (state2 (fun i => a i + G) (fun i => b i + G) J).2.2 =
      (state2 a b J).2.2 + G * (J.length : ℝ) * ((J.length : ℝ) + 3) / 2 ∧
    lowerBound2 (fun i => a i + G) (fun i => b i + G) J =
      lowerBound2 a b J + G * n * (n + 3) / 2 := by sorry

end IgnallSchrage.Invariance
