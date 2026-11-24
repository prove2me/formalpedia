-- Prove2me | Theorems.Thm_LonelyRunnerConjecture_five_runners
-- name    : LonelyRunnerConjecture.five_runners
-- status  : Open
-- author  : @bbchallenge_user
-- created : 2026-11-24T21:04:05.260832+00:00
-- url     : https://prove2.me/theorems/f27bd97c-64fe-4685-bd99-a4a89033f65a
-- title:
--   The lonely runner conjecture for five runners: $\mathrm{LRC}(4)$
-- statement:
--   Here $\|x\|$ denotes the distance from $x \in \mathbb R$ to the nearest integer. The lonely runner conjecture for $k$ moving runners, $\mathrm{LRC}(k)$ (definition `LonelyRunnerConjecture_Defs`), states that for every set $S$ of $k$ distinct positive integers there is $t \in \mathbb R$ with
--   $$\|t v\| \ \ge\ \frac{1}{k+1} \qquad \text{for all } v \in S.$$
--   Together with a stationary runner, this is the case of $k+1$ runners in the Wills–Cusick formulation.
--
--   **Theorem.** $\mathrm{LRC}(4)$ holds: for any 4 distinct positive integer speeds $v_1,\dots,v_4$ there is a time $t$ with $\|t v_i\| \ge 1/5$ for all $i$.
--
--   The case $k=4$ (five runners) is due to Cusick and Pomerance (1984), whose proof used a computer check. A shorter, computer-free proof via nowhere-zero flows was given by Bienia, Goddyn, Gvozdjak, Sebő and Tarsi (1998), who also introduced the runner interpretation.
-- source:
--   T. W. Cusick and C. Pomerance, View-obstruction problems III, J. Number Theory 19 (1984), 131–139; W. Bienia, L. Goddyn, P. Gvozdjak, A. Sebő and M. Tarsi, Flows, view obstructions, and the lonely runner, J. Combin. Theory Ser. B 72 (1998), 1–9.

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs

namespace LonelyRunnerConjecture

theorem five_runners : LRC 4 := by sorry

end LonelyRunnerConjecture
