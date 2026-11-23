-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Main_upper_bound
-- name    : GroupTheoreticShannonCapacity.Main.upper_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:53:01.332063+00:00
-- url     : https://prove2.me/theorems/aff0d914-1055-43f4-8e33-41e57449bc93
-- title:
--   Main: upper bound
-- statement:
--   **Upper Bound**: Θ(E_{p/q}) ≤ p/q.
--
--   Proof: The fractional clique cover number gives χ_f(E_{p/q}) = p/q,
--   and Θ(G) ≤ χ_f(G) for any graph G.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Main.lean#L173-L175
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Main.lean#L173-L175

import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Mathlib.Tactic.Recall
import Definitions.Def_GroupTheoreticShannonCapacity_Main
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Main
open GroupTheoreticShannonCapacity MainProofs Lattice

theorem GroupTheoreticShannonCapacity.Main.upper_bound (p q : ℕ) [NeZero p] (hq : 0 < q) (hpq : q ≤ p) :
    shannonCapacity (fractionGraph p q) ≤ p / q := by sorry
