-- Prove2me | Theorems.Thm_OrderClosures_IsCompleteBooleanSubalgebra_sInf_mem
-- name    : OrderClosures.IsCompleteBooleanSubalgebra.sInf_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:38.913904+00:00
-- url     : https://prove2.me/theorems/41a17e41-7baf-4876-8361-e06ae8caf6e5
-- title:
--   Is Complete Boolean Subalgebra: s Inf mem
-- statement:
--   Derives closure under arbitrary infima from closure under arbitrary
--   suprema and complement; used repeatedly for the generated Boolean algebra.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L294-L306
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L294-L306

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open OrderClosures
universe u
variable (Gamma : Type u) [LinearOrder Gamma] [TopologicalSpace Gamma]
  [DiscreteTopology Gamma]

theorem OrderClosures.IsCompleteBooleanSubalgebra.sInf_mem {B : Type u}
    [CompleteBooleanAlgebra B] {L : BooleanSubalgebra B}
    (hL : IsCompleteBooleanSubalgebra L) (S : Set B) (hSL : S ⊆ L) :
    sInf S ∈ L := by sorry
