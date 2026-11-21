-- Prove2me | Theorems.Thm_GwExact_monoMask_bit
-- name    : GwExact.monoMask_bit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:20:26.263691+00:00
-- url     : https://prove2.me/theorems/9bf8af15-4cb9-463b-a947-151c4d144c9a
-- title:
--   Gw Exact: mono Mask bit
-- statement:
--   The Gw Exact construction uses the mono Mask bit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean#L115-L126
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean#L115-L126

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
public import Definitions.Def_GwExact_Clauses
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.monoMask_bit (R c a d : Nat) : ∀ m j, j < m →
    (monoMask R c a d m).testBit ((a + j * d) * R + c) = true := by sorry
