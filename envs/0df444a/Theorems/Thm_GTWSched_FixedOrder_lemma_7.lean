-- Prove2me | Theorems.Thm_GTWSched_FixedOrder_lemma_7
-- name    : GTWSched.FixedOrder.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:40:04.773515+00:00
-- url     : https://prove2.me/theorems/b1f8b849-65da-4a19-9a4b-0e1c998b44a4
-- title:
--   LEMMA 7, p. 338 — each algorithmic block has more Increase than Decrease tasks or starts at zero
-- statement:
--   Let $a_i\ge0$ and $l_i\ge0$ be the preferred starts and lengths, and let $S_n$ be the schedule produced by the block-shifting algorithm for the first $n$ tasks. For every maximal contiguous block $B=[j,k]$ of $S_n$, either its number of Decrease tasks is strictly less than its number of Increase tasks, or the first task starts at zero:
--
--   $$
--   \operatorname{Dec}(B)<\operatorname{Inc}(B)\quad\text{or}\quad s_j=0.
--   $$
--
--   This is the invariant cited in the correctness proof of the algorithm.
--
--   **Formalization Note** Task $i$ represents the paper's $T_{i+1}$; a block is determined by equality of successive completion and starting times.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 338, LEMMA 7

import Mathlib
import Definitions.Def_GTWSched_FixedOrder_Algorithm

namespace GTWSched.FixedOrder

/-- LEMMA 7, p. 338: every algorithmic block is weighted toward Increase,
unless its first task starts at zero. -/
theorem lemma_7 (a l : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i)
    (n j k : ℕ) (hblock : IsBlock l n (sched a l n) j k) :
    decCount a (sched a l n) j k < incCount a (sched a l n) j k ∨
      sched a l n j = 0 := by sorry

end GTWSched.FixedOrder
