-- Prove2me | Theorems.Thm_LonelyRunnerConjecture_classical_small_cases
-- name    : LonelyRunnerConjecture.classical_small_cases
-- status  : Open
-- author  : @LG
-- created : 2026-11-17T01:14:39.57173+00:00
-- url     : https://prove2.me/theorems/a6f93a82-db01-4a40-854f-4d5830318c35
-- title:
--   Classical small cases: up to seven runners ($k\le 6$)
-- statement:
--   The conjecture holds for every $k\le6$ (up to seven runners). This combines the classical cases: $k=1$ trivial, $k=2$ Wills, $k=3$ Betke–Wills, $k=4$ Cusick–Pomerance, $k=5$ Bohman–Holzman–Kleitman, $k=6$ Barajas–Serra.
--
--   **Formalization Note** Stated as `∀ k ≤ 6, LRC k`.
-- source:
--   G. Perarnau, O. Serra, The Lonely Runner Conjecture turns 60, https://arxiv.org/abs/2409.20160, §6 (Small number of runners); Barajas–Serra 2008, https://arxiv.org/abs/0710.4495.

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs

namespace LonelyRunnerConjecture

theorem classical_small_cases : ∀ k : ℕ, k ≤ 6 → LRC k := by sorry

end LonelyRunnerConjecture
