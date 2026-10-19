-- Prove2me | Theorems.Thm_OAI_Release075_nonsingular_rank_reduction_half
-- name    : OAI.Release075.nonsingular_rank_reduction_half
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:31:16.193251+00:00
-- url     : https://prove2.me/theorems/2a55158a-253b-4166-98a0-90c73233d80e
-- title:
--   Bounded nonsingular integer matrices keep half their rank modulo large primes
-- statement:
--   Let $A$ be a nonsingular $n\times n$ integer matrix, i.e. $\det A\ne0$, and let $r\ge1$ bound the squared norm of every row:
--   $$
--   \sum_jA_{ij}^2\le r\quad\text{for all }i .
--   $$
--   If $q$ is a prime with $r<q$, then the reduction $\bar A$ of $A$ modulo $q$ satisfies
--   $$
--   n\le2\operatorname{rank}\bar A .
--   $$
--
--   So reduction modulo $q$ loses less than half of the rank.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean#L170-L199

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

open OAI OAI.Release075
universe u v
open scoped BigOperators

theorem OAI.Release075.nonsingular_rank_reduction_half {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hdet : A.det ≠ 0) (r : ℝ) (hr : 1 ≤ r)
    (hrow : ∀ i, ∑ j, (A i j : ℝ) ^ 2 ≤ r)
    (q : ℕ) [Fact q.Prime] (hqr : r < q) :
    n ≤ 2 * (A.map (Int.cast : ℤ → ZMod q)).rank := by sorry
