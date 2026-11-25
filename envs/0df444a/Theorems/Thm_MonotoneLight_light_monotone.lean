-- Prove2me | Theorems.Thm_MonotoneLight_light_monotone
-- name    : MonotoneLight.light_monotone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:28.856579+00:00
-- url     : https://prove2.me/theorems/10386258-155c-4575-b437-ff152c7eb9b5
-- title:
--   Monotone Light: light monotone
-- statement:
--   The Monotone Light construction uses the light monotone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L183-L184
-- source:
--   https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L183-L184

module
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import Definitions.Def_MonotoneLight_Solution
set_option autoImplicit true
@[expose] public section
public section
open Set Function Topology
universe u v
open MonotoneLight
variable {X : Type u} {Y : Type v} [_tX : TopologicalSpace X] [_tY : TopologicalSpace Y]
omit [TopologicalSpace Y]

theorem MonotoneLight.light_monotone (f : X → Y) (x : X) :
    light f (monotone f x) = f x := by sorry

attribute [defeq] MonotoneLight.light_monotone
