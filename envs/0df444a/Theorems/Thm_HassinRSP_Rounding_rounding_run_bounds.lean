-- Prove2me | Theorems.Thm_HassinRSP_Rounding_rounding_run_bounds
-- name    : HassinRSP.Rounding.rounding_run_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:25:20.570773+00:00
-- url     : https://prove2.me/theorems/ebac1578-86a7-494f-8322-514c3469d5a4
-- title:
--   §4, p. 39 — along the Rounding Algorithm, LB stays a positive lower bound on OPT and UB an upper bound
-- statement:
--   Consider an instance of the restricted shortest path problem (vertices $1,\dots,n$, $n\ge2$, edges $(i,j)$ with $i<j$, positive integer lengths and transition times), a time budget $T$ and $\varepsilon>0$. Run Step 1 of the Rounding Algorithm from initial bounds $(LB_0,UB_0)$, where $LB_0>0$ and every $T$-path has length at least $LB_0$, and let $(LB_k,UB_k)$ be the bounds after $k$ passes: each pass with $UB>2LB$ tests $V=(LB\cdot UB)^{1/2}$ and sets $LB\leftarrow V$ on YES, $UB\leftarrow V(1+\varepsilon)$ on NO.
--
--   Then for every $k$:
--   1. $LB_k>0$;
--   2. every $T$-path $q$ satisfies $LB_k\le c(q)$;
--   3. if some $T$-path has length at most $UB_0$, then some $T$-path has length at most $UB_k$.
--
--   This is the paper's "TEST(V) can be applied now to improve the bounds on OPT. Specifically either LB is increased to $V$ or UB is decreased to $V(1+\varepsilon)$": the bounds remain valid bounds on OPT throughout the run.
--
--   **Formalization Note.** "LB $\le$ OPT" is stated as a bound on every $T$-path, and "OPT $\le$ UB" as the existence of a $T$-path of length at most UB, assumed at the start and concluded at every stage. The hypothesis $\varepsilon<1$ is not needed and is omitted; $UB_0$ is arbitrary.
-- source:
--   Hassin, Approximation schemes for the restricted shortest path problem, Math. Oper. Res. 17 (1992), p. 39, §4, second paragraph and Rounding Algorithm Step 1

import Mathlib
import Definitions.Def_HassinRSP_Rounding_Setting

namespace HassinRSP.Rounding

theorem rounding_run_bounds (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ)
    (hε0 : 0 < ε) (LB0 UB0 : ℝ) (hLB0 : 0 < LB0)
    (hLB0_le : ∀ q, IsTPath I T q → LB0 ≤ pathLen I q) (k : ℕ) :
    0 < (roundingRun I T ε LB0 UB0 k).1 ∧
    (∀ q, IsTPath I T q → (roundingRun I T ε LB0 UB0 k).1 ≤ pathLen I q) ∧
    ((∃ q, IsTPath I T q ∧ (pathLen I q : ℝ) ≤ UB0) →
      ∃ q, IsTPath I T q ∧ (pathLen I q : ℝ) ≤ (roundingRun I T ε LB0 UB0 k).2) := by sorry

end HassinRSP.Rounding
