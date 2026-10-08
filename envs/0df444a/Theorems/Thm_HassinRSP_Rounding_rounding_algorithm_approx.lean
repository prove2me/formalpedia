-- Prove2me | Theorems.Thm_HassinRSP_Rounding_rounding_algorithm_approx
-- name    : HassinRSP.Rounding.rounding_algorithm_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:27:56.736643+00:00
-- url     : https://prove2.me/theorems/fa16e6fa-fa8e-4bde-ba39-c27833d9f4cb
-- title:
--   §4, Rounding Algorithm, p. 39 — once UB ≤ 2LB, a T-path optimal for ⌊c_ij(n − 1)/εLB⌋ has length ≤ (1 + ε)·OPT
-- statement:
--   Consider an instance of the restricted shortest path problem: a directed graph on vertices $1,\dots,n$ ($n\ge2$) whose edges $(i,j)$ satisfy $i<j$, with positive integer lengths $c_{ij}$ and transition times $t_{ij}$, a time budget $T$, and a fixed $0<\varepsilon<1$. A $T$-path is a $1$–$n$ path of transition time at most $T$; OPT is the length of a shortest one.
--
--   Run Hassin's Rounding Algorithm:
--   1. Step 0: start with bounds $LB_0>0$ and $UB_0$, where every $T$-path has length at least $LB_0$.
--   2. Step 1: while $UB>2LB$, let $V=(LB\cdot UB)^{1/2}$; set $LB\leftarrow V$ if TEST(V) = YES and $UB\leftarrow V(1+\varepsilon)$ if TEST(V) = NO.
--   3. Step 2: when $UB\le 2LB$ (say after $N$ passes, with lower bound $LB_N$), output a $T$-path $p$ that is optimal for the rounded lengths $\lfloor c_{ij}(n-1)/(\varepsilon LB_N)\rfloor$.
--
--   Then the output is a $(1+\varepsilon)$-approximation: for every $T$-path $q$,
--   $$c(p)\le(1+\varepsilon)\,c(q),$$
--   that is, $c(p)\le(1+\varepsilon)\,\mathrm{OPT}$.
--
--   This is the approximation guarantee of the first fully polynomial approximation scheme of the paper (§3–§4), built on rounding and scaling of the edge lengths together with a geometric search for a lower bound on OPT.
--
--   **Formalization Note.** OPT is expressed through $T$-paths (it is $\infty$ when no $T$-path exists, in which case there is no output path and nothing to prove). TEST(V) is the decision procedure of §3, defined by its answer. The statement covers every stage $N$ at which the stopping test $UB_N\le2LB_N$ holds and every Step 2 output; no assumption on $UB_0$ is made. The stopping test need not be reached when $(1+\varepsilon)^2>2$; see the companion statements on termination. Running times are not formalized.
-- source:
--   Hassin, Approximation schemes for the restricted shortest path problem, Math. Oper. Res. 17 (1992), p. 39, §4, Rounding Algorithm, with Procedure TEST(V) of §3, p. 38

import Mathlib
import Definitions.Def_HassinRSP_Rounding_Setting

namespace HassinRSP.Rounding

theorem rounding_algorithm_approx (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (LB0 UB0 : ℝ) (hLB0 : 0 < LB0)
    (hLB0_le : ∀ q, IsTPath I T q → LB0 ≤ pathLen I q) (N : ℕ)
    (hstop : (roundingRun I T ε LB0 UB0 N).2 ≤ 2 * (roundingRun I T ε LB0 UB0 N).1)
    (p : List ℕ) (hp : IsRoundingOutput I T ε (roundingRun I T ε LB0 UB0 N).1 p) :
    ∀ q, IsTPath I T q → (pathLen I p : ℝ) ≤ (1 + ε) * pathLen I q := by sorry

end HassinRSP.Rounding
