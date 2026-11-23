-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Main_limit_fraction_graphs
-- name    : GroupTheoreticShannonCapacity.Main.limit_fraction_graphs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:52:25.476896+00:00
-- url     : https://prove2.me/theorems/ab8dee48-439e-480b-bab3-505d8499b7b4
-- title:
--   Main: limit fraction graphs
-- statement:
--   **Theorem 1.2**: The Shannon capacity of E_{p/q} approaches p/q as p/q → ∞.
--
--   $$\lim_{p/q \to \infty} p/q - \Theta(E_{p/q}) = 0$$
--
--   This strengthens Theorem 1.1 since E_{p/2} = C_p.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Main.lean#L117-L120
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Main.lean#L117-L120

import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Mathlib.Tactic.Recall
import Definitions.Def_GroupTheoreticShannonCapacity_Main
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Main
open GroupTheoreticShannonCapacity MainProofs Lattice

theorem GroupTheoreticShannonCapacity.Main.limit_fraction_graphs (ε : ℝ) (hε : ε > 0) :
    ∃ M : ℝ, ∀ p q : ℕ, [NeZero p] → (q : ℝ) > 0 → (p : ℝ) / q > M →
      |(p : ℝ) / q - shannonCapacity (fractionGraph p q)| < ε := by sorry
