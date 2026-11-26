-- Prove2me | Theorems.Thm_N4Code_abel_sum
-- name    : N4Code.abel_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:04:29.219055+00:00
-- url     : https://prove2.me/theorems/06cc5122-96e6-5246-beac-a0006fb4b2e6
-- title:
--   N4 Code: abel sum
-- statement:
--   Abel summation: Σ a_d r^(d−1) = Ψ_n r^(n−1) + Σ_{d<n} Ψ_d (r^(d−1) − r^d),
--   where Ψ_d = Σ_{i≤d} a_i (paper `cor:1` (Corollary 21)).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L1138-L1256
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L1138-L1256

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.abel_sum {n : ℕ} (a : ℕ → ℝ) (r : ℝ) :
    (∑ d ∈ Finset.Icc 1 n, a d * r ^ (d - 1)) =
      (∑ i ∈ Finset.Icc 1 n, a i) * r ^ (n - 1) +
        ∑ d ∈ Finset.Icc 1 (n - 1), (∑ i ∈ Finset.Icc 1 d, a i) * (r ^ (d - 1) - r ^ d) := by sorry
