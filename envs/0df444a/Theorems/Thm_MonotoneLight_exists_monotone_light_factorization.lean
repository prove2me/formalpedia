-- Prove2me | Theorems.Thm_MonotoneLight_exists_monotone_light_factorization
-- name    : MonotoneLight.exists_monotone_light_factorization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T08:41:42.746053+00:00
-- url     : https://prove2.me/theorems/0aa0dcad-ff24-4097-8fb2-41a823cb44fa
-- title:
--   Monotone Light: exists monotone light factorization
-- statement:
--   Every continuous surjection of compact Hausdorff spaces has a monotone-light
--   factorization. The final equivalence specifies exactly which points the quotient identifies.
--   Empty spaces are permitted.
--
--   Source: https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L230-L242
-- source:
--   https://github.com/Arthur742Ramos/monotone-light-factorization-lean/blob/759906c53ae14a660ab0e473dcf075d859c5a5a9/Solution.lean#L230-L242

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

theorem MonotoneLight.exists_monotone_light_factorization [_cX : CompactSpace X] [_hX : T2Space X]
    [_cY : CompactSpace Y] [_hY : T2Space Y] {f : X → Y} (hf : Continuous f) (hs : Surjective f) :
    ∃ (Z : Type u) (tZ : TopologicalSpace Z), letI := tZ;
      CompactSpace Z ∧ T2Space Z ∧ ∃ (m : X → Z) (l : Z → Y),
        Continuous m ∧ Surjective m ∧ Continuous l ∧ Surjective l ∧
        f = l ∘ m ∧ (∀ z, IsConnected (m ⁻¹' {z})) ∧
        (∀ y, IsTotallyDisconnected (l ⁻¹' {y})) ∧
        (∀ x y, m x = m y ↔ FiberRel f x y) := by sorry
