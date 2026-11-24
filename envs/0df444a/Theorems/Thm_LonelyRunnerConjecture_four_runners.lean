-- Prove2me | Theorems.Thm_LonelyRunnerConjecture_four_runners
-- name    : LonelyRunnerConjecture.four_runners
-- status  : Proved
-- author  : @bbchallenge_user
-- created : 2026-11-24T21:04:15.956018+00:00
-- url     : https://prove2.me/theorems/7727783e-7514-4c59-8ed1-c08bc06e0606
-- title:
--   The lonely runner conjecture for four runners: $\mathrm{LRC}(3)$
-- statement:
--   Here $\|x\|$ denotes the distance from $x \in \mathbb R$ to the nearest integer. The lonely runner conjecture for $k$ moving runners, $\mathrm{LRC}(k)$ (definition `LonelyRunnerConjecture_Defs`), states that for every set $S$ of $k$ distinct positive integers there is $t \in \mathbb R$ with
--   $$\|t v\| \ \ge\ \frac{1}{k+1} \qquad \text{for all } v \in S.$$
--   Together with a stationary runner, this is the case of $k+1$ runners in the Wills–Cusick formulation.
--
--   **Theorem.** $\mathrm{LRC}(3)$ holds: for any 3 distinct positive integer speeds $v_1,\dots,v_3$ there is a time $t$ with $\|t v_i\| \ge 1/4$ for all $i$.
--
--   The case $k=3$ (four runners) was first proved by Betke and Wills (1972) and independently by Cusick (1974), in the language of Diophantine approximation and view-obstruction respectively. It is one of the four classical cases that, together with the elementary cases $k \le 2$, make up the milestone `classical_small_cases` ($k \le 6$).
-- source:
--   U. Betke and J. M. Wills, Untere Schranken für zwei diophantische Approximations-Funktionen, Monatsh. Math. 76 (1972), 214–217; T. W. Cusick, View-obstruction problems in n-dimensional geometry, J. Combin. Theory Ser. A 16 (1974), 1–11. Survey: G. Perarnau and O. Serra, Section 6.

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs

namespace LonelyRunnerConjecture

theorem four_runners : LRC 3 := by sorry

end LonelyRunnerConjecture
