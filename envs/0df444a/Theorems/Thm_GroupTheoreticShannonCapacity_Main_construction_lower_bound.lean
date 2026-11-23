-- Prove2me | Theorems.Thm_GroupTheoreticShannonCapacity_Main_construction_lower_bound
-- name    : GroupTheoreticShannonCapacity.Main.construction_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:02:37.836327+00:00
-- url     : https://prove2.me/theorems/d25aeeb1-7f35-4a27-bea6-1fcc356059ef
-- title:
--   Main: construction lower bound
-- statement:
--   **Theorem 1.7**: For nonnegative integers n, k, b, r, s with
--   n, k, b ≥ 1 and r ≤ b, the parametric construction gives:
--
--   $$\alpha_g(E_{p/q}^{\boxtimes n}) \geq p$$
--
--   where p, q are determined by the construction parameters. This yields
--   Θ(E_{p/q}) ≥ p^{1/n}.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Main.lean#L144-L151
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Main.lean#L144-L151

import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Mathlib.Tactic.Recall
import Definitions.Def_GroupTheoreticShannonCapacity_Main
import Theorems.Thm_GroupTheoreticShannonCapacity_MainProofs_construction_lower_bound

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Main
open GroupTheoreticShannonCapacity MainProofs Lattice

theorem GroupTheoreticShannonCapacity.Main.construction_lower_bound (n k b r s : ℕ) [NeZero n]
    (hk : 1 ≤ k) (hb : 1 ≤ b) (hrb : r ≤ b) :
    have pVal := Construction.p n k b r s
    have qVal := Construction.q n k b r s
    ∃ p' q' : ℕ, ∃ (_ : NeZero p') (_ : 0 < q'),
      (p' : ℚ) = pVal ∧ (q' : ℚ) = qVal ∧
      shannonCapacity (fractionGraph p' q') ≥ (p' : ℝ) ^ (1 / (n : ℝ)) := by sorry
