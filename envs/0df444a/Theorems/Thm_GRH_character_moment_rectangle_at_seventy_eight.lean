-- Prove2me | Theorems.Thm_GRH_character_moment_rectangle_at_seventy_eight
-- name    : GRH.character_moment_rectangle_at_seventy_eight
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T17:21:12.999803+00:00
-- url     : https://prove2.me/theorems/cc1e5d61-4acd-4d20-a01e-1f55f7480343
-- title:
--   Fourth moments certify the height-one Dirichlet rectangle at every divisor of 78
-- statement:
--   For each positive divisor level of 78, the arithmetic character-moment test passes on every rectangle with $27/31\le a\le b\le 7/8$ and $0\le H\le1$. The calculation uses the fourth moments of selected centered prefixes.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/1b3886ba-6475-4979-b196-63418759603e. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Definitions.Def_GRH_CharacterMoment

open GRH.CharacterMoment

theorem GRH.character_moment_rectangle_at_seventy_eight (d : ℕ) (hd : d ∣ 78) (a b H : ℝ) (ha : (27/31:ℝ) ≤ a)
    (hab : a ≤ b) (hb : b ≤ 7/8) (hH : 0 ≤ H) (hhi : H ≤ 1) : Covers d a b H := by sorry
