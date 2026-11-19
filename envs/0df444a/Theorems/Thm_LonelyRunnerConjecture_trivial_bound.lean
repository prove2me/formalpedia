-- Prove2me | Theorems.Thm_LonelyRunnerConjecture_trivial_bound
-- name    : LonelyRunnerConjecture.trivial_bound
-- status  : Proved
-- author  : @LG
-- created : 2026-11-17T01:12:07.287907+00:00
-- url     : https://prove2.me/theorems/85b80cd9-fdcb-4fdf-9b95-f252185e4c14
-- title:
--   Trivial union bound $\delta_k \ge 1/(2k)$
-- statement:
--   For every $k\ge1$ and any $k$ distinct positive integer speeds, there is a time $t$ at which every runner is at distance at least $\frac{1}{2k}$ from the start. This is the trivial union-bound lower bound on the gap of loneliness, a factor of two short of the conjecture.
--
--   **Formalization Note** Stated for a `Finset ℕ` of cardinality $k$ with positive speeds; the bound is `(1:ℝ)/(2*k)`.
-- source:
--   T. Tao, Some remarks on the lonely runner conjecture, https://arxiv.org/abs/1701.02048 (v4), Proposition 1.1.

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs

namespace LonelyRunnerConjecture

theorem trivial_bound (k : ℕ) (hk : 1 ≤ k) (S : Finset ℕ) (hS : S.card = k)
    (hpos : ∀ v ∈ S, 0 < v) :
    ∃ t : ℝ, ∀ v ∈ S, (1 : ℝ) / (2 * k : ℝ) ≤ distToNearestInt (t * (v : ℝ)) := by sorry

end LonelyRunnerConjecture
