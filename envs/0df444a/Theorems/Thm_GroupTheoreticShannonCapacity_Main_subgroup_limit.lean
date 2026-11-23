-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Main_subgroup_limit
-- name    : GroupTheoreticShannonCapacity.Main.subgroup_limit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:52:52.63574+00:00
-- url     : https://prove2.me/theorems/e62c1b90-c286-4995-8121-26e16bdf849b
-- title:
--   Main: subgroup limit
-- statement:
--   **Theorem 1.3**: For every ε > 0, for all p/q large enough, there exist a, b ∈ ℕ
--   such that a/b = p/q and p/q - Θ_g(E_{a/b}) < ε.
--
--   This shows the limit can be achieved via subgroup independent sets.
--   Note that Θ_g(E_{p/q}) may differ for equivalent fractions a/b = p/q.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Main.lean#L129-L133
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Main.lean#L129-L133

import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Mathlib.Tactic.Recall
import Definitions.Def_GroupTheoreticShannonCapacity_Main
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Main
open GroupTheoreticShannonCapacity MainProofs Lattice

theorem GroupTheoreticShannonCapacity.Main.subgroup_limit (ε : ℝ) (hε : ε > 0) :
    ∃ M : ℝ, ∀ p q : ℕ, p ≠ 0 → 0 < q → (p : ℝ) / q > M →
      ∃ (a b : ℕ) (_ : NeZero a), (a : ℚ) / b = (p : ℚ) / q ∧
        (p : ℝ) / q - addSubgroupShannonCapacity (fractionGraph a b) < ε := by sorry
