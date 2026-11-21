-- Prove2me | Theorems.Thm_GwExact_goodPos_of_colouring
-- name    : GwExact.goodPos_of_colouring
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:22:14.038892+00:00
-- url     : https://prove2.me/theorems/76a96a1a-a3bf-4e8e-8334-6e0f1b643829
-- title:
--   Gw Exact: good Pos of colouring
-- statement:
--   **Bridge.** A colouring `c : ℕ → Fin r` with `r ≤ R`, no rainbow 3-term AP and no monochromatic
--   `l`-term AP in `[1, n]`, renamed in order of first appearance, has the properties `GoodPos n R l`
--   on the positions `0, …, n - 1` (position `i` is the point `i + 1`).
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L143-L167
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Rank.lean#L143-L167

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_GwExact_Rank
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.goodPos_of_colouring {r R l n : ℕ} (hrR : r ≤ R) (c : ℕ → Fin r)
    (hrb : ∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + 2 * d ≤ n →
      ¬ (c x ≠ c (x + d) ∧ c x ≠ c (x + 2 * d) ∧ c (x + d) ≠ c (x + 2 * d)))
    (hmono : ∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ n → ¬ ∀ j < l, c (x + j * d) = c x) :
    GoodPos n R l (rank fun i => c (i + 1)) := by sorry
