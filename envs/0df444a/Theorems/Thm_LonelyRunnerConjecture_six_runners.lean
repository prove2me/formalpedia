-- Prove2me | Theorems.Thm_LonelyRunnerConjecture_six_runners
-- name    : LonelyRunnerConjecture.six_runners
-- status  : Open
-- author  : @bbchallenge_user
-- created : 2026-11-24T21:04:12.337686+00:00
-- url     : https://prove2.me/theorems/d434ed65-50ff-4559-92d5-6e630017ac13
-- title:
--   The lonely runner conjecture for six runners: $\mathrm{LRC}(5)$
-- statement:
--   Here $\|x\|$ denotes the distance from $x \in \mathbb R$ to the nearest integer. The lonely runner conjecture for $k$ moving runners, $\mathrm{LRC}(k)$ (definition `LonelyRunnerConjecture_Defs`), states that for every set $S$ of $k$ distinct positive integers there is $t \in \mathbb R$ with
--   $$\|t v\| \ \ge\ \frac{1}{k+1} \qquad \text{for all } v \in S.$$
--   Together with a stationary runner, this is the case of $k+1$ runners in the Wills–Cusick formulation.
--
--   **Theorem.** $\mathrm{LRC}(5)$ holds: for any 5 distinct positive integer speeds $v_1,\dots,v_5$ there is a time $t$ with $\|t v_i\| \ge 1/6$ for all $i$.
--
--   The case $k=5$ (six runners) was proved by Bohman, Holzman and Kleitman (2001); Renault (2004) later gave a shorter proof.
-- source:
--   T. Bohman, R. Holzman and D. Kleitman, Six lonely runners, Electron. J. Combin. 8(2) (2001), #R3; J. Renault, View-obstruction: a shorter proof for 6 lonely runners, Discrete Math. 287 (2004), 93–101.

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs

namespace LonelyRunnerConjecture

theorem six_runners : LRC 5 := by sorry

end LonelyRunnerConjecture
