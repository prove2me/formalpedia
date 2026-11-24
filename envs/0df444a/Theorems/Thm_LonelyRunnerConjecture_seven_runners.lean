-- Prove2me | Theorems.Thm_LonelyRunnerConjecture_seven_runners
-- name    : LonelyRunnerConjecture.seven_runners
-- status  : Open
-- author  : @bbchallenge_user
-- created : 2026-11-24T21:04:16.279717+00:00
-- url     : https://prove2.me/theorems/2a232721-a631-49ca-bb0d-d7dffdc62f49
-- title:
--   The lonely runner conjecture for seven runners: $\mathrm{LRC}(6)$
-- statement:
--   Here $\|x\|$ denotes the distance from $x \in \mathbb R$ to the nearest integer. The lonely runner conjecture for $k$ moving runners, $\mathrm{LRC}(k)$ (definition `LonelyRunnerConjecture_Defs`), states that for every set $S$ of $k$ distinct positive integers there is $t \in \mathbb R$ with
--   $$\|t v\| \ \ge\ \frac{1}{k+1} \qquad \text{for all } v \in S.$$
--   Together with a stationary runner, this is the case of $k+1$ runners in the Wills–Cusick formulation.
--
--   **Theorem.** $\mathrm{LRC}(6)$ holds: for any 6 distinct positive integer speeds $v_1,\dots,v_6$ there is a time $t$ with $\|t v_i\| \ge 1/7$ for all $i$.
--
--   The case $k=6$ (seven runners) was proved by Barajas and Serra (2008). It was the largest settled case until the computer-assisted proof for eight runners by Rosenfeld (2025).
-- source:
--   J. Barajas and O. Serra, The lonely runner with seven runners, Electron. J. Combin. 15 (2008), #R48.

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs

namespace LonelyRunnerConjecture

theorem seven_runners : LRC 6 := by sorry

end LonelyRunnerConjecture
