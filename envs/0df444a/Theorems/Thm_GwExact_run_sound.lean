-- Prove2me | Theorems.Thm_GwExact_run_sound
-- name    : GwExact.run_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:19:51.376399+00:00
-- url     : https://prove2.me/theorems/d3d902fe-ea2b-4563-80f8-8ea314cc70e3
-- title:
--   Gw Exact: run sound
-- statement:
--   Soundness of the main loop: if every clause the source returns (for a trie of true clauses)
--   is true under `σ`, no run succeeds.
--
--   Source: https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L352-L387
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean#L352-L387

module
public import Definitions.Def_GwExact_Check
set_option autoImplicit true
@[expose] public section
public section
open GwExact

theorem GwExact.run_sound {σ : Nat → Bool} {src : Trie → Nat → Option Cls} {w wm : Nat}
    (hsrc : ∀ db, Good σ db → ∀ h c, src db h = some c → c.Holds σ) :
    ∀ (steps : List Nat) (db : Trie) (i : Nat), Good σ db → run src w wm db i steps = true → False := by sorry
