-- Prove2me | Theorems.Thm_N4Code_count_words_with_prescribed_weights
-- name    : N4Code.count_words_with_prescribed_weights
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:14.046407+00:00
-- url     : https://prove2.me/theorems/bd2fb0b4-ecfe-5726-b243-e366793f15dc
-- title:
--   N4 Code: count words with prescribed weights
-- statement:
--   The number of words with prescribed per-type weights is the product of
--   binomials: Π_i C(|i|, k_i) (paper §3.1 counting fact).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L575-L583
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L575-L583

import Definitions.Def_N4Code_Definitions
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Definitions.Def_N4Code_Basic
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code

theorem N4Code.count_words_with_prescribed_weights {n : ℕ} (C : Code n) (k : ℕ → ℕ) :
    ((Finset.univ : Finset (Word n)).filter
        fun y : Word n => (∑ i ∈ Finset.Icc 0 15, if w_i C i y = k i then 0 else 1) = 0).card =
      ∏ i ∈ Finset.Icc 0 15, Nat.choose (count C i) (k i) := by sorry
