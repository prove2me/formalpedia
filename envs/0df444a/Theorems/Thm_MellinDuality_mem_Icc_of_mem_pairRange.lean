-- Prove2me | Theorems.Thm_MellinDuality_mem_Icc_of_mem_pairRange
-- name    : MellinDuality.mem_Icc_of_mem_pairRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:40.249683+00:00
-- url     : https://prove2.me/theorems/ceaf5ef0-0a88-49b3-8f4b-802b086d3c1a
-- title:
--   Mellin Duality: mem Icc of mem pair Range
-- statement:
--   The Mellin Duality construction uses the mem Icc of mem pair Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Pairs.lean#L105-L108
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Pairs.lean#L105-L108

module
public import Definitions.Def_MellinDuality_Quartic
public import Definitions.Def_MellinDuality_Parseval
public import Definitions.Def_MellinDuality_Pairs
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.mem_Icc_of_mem_pairRange {N : ℕ} {ab : ℕ × ℕ} {r : ℕ}
    (hr : r ∈ pairRange N ab) : r ∈ Icc 1 N := by sorry
