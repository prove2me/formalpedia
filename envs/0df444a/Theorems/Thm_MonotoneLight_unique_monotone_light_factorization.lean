-- Prove2me | Theorems.Thm_MonotoneLight_unique_monotone_light_factorization
-- name    : MonotoneLight.unique_monotone_light_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:41:48.269632+00:00
-- url     : https://prove2.me/theorems/1acf6513-bd38-412b-b29a-fa3a60de5adb
-- title:
--   Monotone Light: unique monotone light factorization
-- statement:
--   Any two monotone-light factorizations are related by exactly one commuting
--   homeomorphism. No nonemptiness premise is needed.
--
--   Source: https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L274-L320
-- source:
--   https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L274-L320

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

theorem MonotoneLight.unique_monotone_light_factorization [_cX : CompactSpace X] [_hX : T2Space X]
    [_cY : CompactSpace Y] [_hY : T2Space Y]
    {Z W : Type*} [_tZ : TopologicalSpace Z] [_tW : TopologicalSpace W]
    [_cZ : CompactSpace Z] [_hZ : T2Space Z] [_cW : CompactSpace W] [_hW : T2Space W]
    {f : X → Y} {m : X → Z} {l : Z → Y} {n : X → W} {k : W → Y}
    (hm : Continuous m) (hn : Continuous n) (hms : Surjective m) (hns : Surjective n)
    (hfm : f = l ∘ m) (hfn : f = k ∘ n)
    (hmc : ∀ z, IsConnected (m ⁻¹' {z})) (hnc : ∀ w, IsConnected (n ⁻¹' {w}))
    (hl : ∀ y, IsTotallyDisconnected (l ⁻¹' {y}))
    (hk : ∀ y, IsTotallyDisconnected (k ⁻¹' {y})) :
    ∃! h : Z ≃ₜ W, (fun x => h (m x)) = n ∧ l = k ∘ h := by sorry
