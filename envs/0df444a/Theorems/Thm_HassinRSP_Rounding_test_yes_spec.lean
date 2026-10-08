-- Prove2me | Theorems.Thm_HassinRSP_Rounding_test_yes_spec
-- name    : HassinRSP.Rounding.test_yes_spec
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:24:53.146988+00:00
-- url     : https://prove2.me/theorems/95bf91ba-8c15-477a-b128-64aac4f773c1
-- title:
--   §3, TEST(V), second case, p. 38 — if TEST(V) = YES, every T-path has length ≥ V
-- statement:
--   Consider an instance of the restricted shortest path problem (vertices $1,\dots,n$, $n\ge2$, edges $(i,j)$ with $i<j$, positive integer lengths $c_{ij}$ and transition times $t_{ij}$), a time budget $T$, $\varepsilon>0$ and a real $V$. Hassin's test is specified at the top of §3: "This test has the following properties: If it outputs a positive answer then definitely OPT $\geqslant V$. If it outputs a negative answer, then all we know is that OPT $< V(1+\varepsilon)$." This statement is the positive half.
--
--   If TEST(V) outputs YES — that is, for no integer $c<(n-1)/\varepsilon$ is there a $1$–$n$ path using only edges with $c_{ij}\le V$, of transition time at most $T$ and rounded length $\sum\lfloor c_{ij}(n-1)/(V\varepsilon)\rfloor\le c$ — then every $T$-path $q$ satisfies
--   $$c(q)\ge V .$$
--
--   In particular OPT $\ge V$. The conclusion covers all $T$-paths, including those through edges with $c_{ij}>V$ that TEST deletes. This is what allows the Rounding Algorithm to raise its lower bound to $V$ after a YES answer.
--
--   **Formalization Note.** "OPT $\ge V$" is expressed as a bound on every $T$-path, so it holds vacuously, as it should, when no $T$-path exists. The hypotheses $V>0$ and $\varepsilon<1$ are not needed and are omitted.
-- source:
--   Hassin, Approximation schemes for the restricted shortest path problem, Math. Oper. Res. 17 (1992), p. 38, §3, specification of the ε-approximation test and its 'second case', Procedure TEST(V)

import Mathlib
import Definitions.Def_HassinRSP_Rounding_Setting

namespace HassinRSP.Rounding

theorem test_yes_spec (I : Instance) (hI : I.WellFormed) (T : ℕ) (ε : ℝ) (hε0 : 0 < ε)
    (V : ℝ) :
    testYes I T ε V → ∀ q, IsTPath I T q → V ≤ pathLen I q := by sorry

end HassinRSP.Rounding
