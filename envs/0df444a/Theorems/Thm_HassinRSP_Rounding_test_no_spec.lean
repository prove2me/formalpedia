-- Prove2me | Theorems.Thm_HassinRSP_Rounding_test_no_spec
-- name    : HassinRSP.Rounding.test_no_spec
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:24:45.752508+00:00
-- url     : https://prove2.me/theorems/599121f9-2958-4f4f-9089-08675da7acb4
-- title:
--   §3, TEST(V), first case, p. 38 — if TEST(V) = NO, a T-path of length < V(1 + ε) exists
-- statement:
--   Consider an instance of the restricted shortest path problem (vertices $1,\dots,n$, $n\ge2$, edges $(i,j)$ with $i<j$, positive integer lengths $c_{ij}$ and transition times $t_{ij}$), a time budget $T$, $\varepsilon>0$ and a real $V$. Hassin's test is specified at the top of §3: "This test has the following properties: If it outputs a positive answer then definitely OPT $\geqslant V$. If it outputs a negative answer, then all we know is that OPT $< V(1+\varepsilon)$." This statement is the negative half.
--
--   If TEST(V) outputs NO — that is, for some integer $\hat c<(n-1)/\varepsilon$ there is a $1$–$n$ path using only edges with $c_{ij}\le V$, of transition time at most $T$ and of rounded length $\sum\lfloor c_{ij}(n-1)/(V\varepsilon)\rfloor\le\hat c$ — then there is a $T$-path $q$ with
--   $$c(q)<V(1+\varepsilon).$$
--
--   In particular OPT $<V(1+\varepsilon)$. The paper obtains the path's length bound $\frac{V\varepsilon}{n-1}\hat c+V\varepsilon<V(1+\varepsilon)$. This is what allows the Rounding Algorithm to lower its upper bound to $V(1+\varepsilon)$ after a NO answer.
--
--   **Formalization Note.** OPT is not a Lean term (it is $\infty$ when no $T$-path exists); "OPT $<V(1+\varepsilon)$" is expressed by exhibiting a $T$-path. The hypotheses $V>0$ and $\varepsilon<1$ are not needed and are omitted: for $V\le0$ no edge survives the pruning, so TEST(V) never answers NO.
-- source:
--   Hassin, Approximation schemes for the restricted shortest path problem, Math. Oper. Res. 17 (1992), p. 38, §3, specification of the ε-approximation test and its 'first case', Procedure TEST(V)

import Mathlib
import Definitions.Def_HassinRSP_Rounding_Setting

namespace HassinRSP.Rounding

theorem test_no_spec (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ) (hε0 : 0 < ε)
    (V : ℝ) :
    testNo I T ε V → ∃ q, IsTPath I T q ∧ (pathLen I q : ℝ) < V * (1 + ε) := by sorry

end HassinRSP.Rounding
