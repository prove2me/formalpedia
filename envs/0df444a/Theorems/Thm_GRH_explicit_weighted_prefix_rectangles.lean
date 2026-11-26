-- Prove2me | Theorems.Thm_GRH_explicit_weighted_prefix_rectangles
-- name    : GRH.explicit_weighted_prefix_rectangles
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T16:15:51.09924+00:00
-- url     : https://prove2.me/theorems/8f661244-080b-564d-a614-7fdc56e90f01
-- title:
--   Explicit character-prefix tables certify nineteen unit-height levels and a height-three family
-- statement:
--   For every divisor of $24,36,42$, or $60$, the weighted-prefix test passes throughout $27/31\le a\le b\le7/8$ and $0\le H\le1$. For divisors of $6$ it passes throughout $8/13\le a\le b\le7/8$, $0\le H\le3$. The proof checks all entries and error budgets of five finite rational witnesses.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/59bf325f-868f-5552-94bb-1b5f67435396. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Definitions.Def_GRH_DirichletPrefix

open GRH.DirichletPrefix

theorem GRH.explicit_weighted_prefix_rectangles (d : ℕ) (a b H : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 7/8)
    (hH : 0 ≤ H) (h : ((d ∣ 24 ∨ d ∣ 36 ∨ d ∣ 42 ∨ d ∣ 60) ∧ (27/31:ℝ) ≤ a ∧ H ≤ 1) ∨
      (d ∣ 6 ∧ (8/13:ℝ) ≤ a ∧ H ≤ 3)) : Covers d a b H := by sorry
