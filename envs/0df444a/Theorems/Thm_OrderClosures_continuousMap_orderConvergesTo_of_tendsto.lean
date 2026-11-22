-- Prove2me | Theorems.Thm_OrderClosures_continuousMap_orderConvergesTo_of_tendsto
-- name    : OrderClosures.continuousMap_orderConvergesTo_of_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:32.365544+00:00
-- url     : https://prove2.me/theorems/bb3c5078-d7ac-48f3-84dc-f464eb3c3ec5
-- title:
--   Order Closures: continuous Map order Converges To of tendsto
-- statement:
--   Converts uniform convergence with a summable error bound into order
--   convergence; used to show order-closed sublattices are norm closed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1351-L1409
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1351-L1409

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
universe u v
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]

theorem OrderClosures.continuousMap_orderConvergesTo_of_tendsto
    {ι : Type v} [Preorder ι] {f : ι → C(K, ℝ)} {x : C(K, ℝ)}
    (hfx : Filter.Tendsto f Filter.atTop (nhds x)) :
    OrderConvergesTo f x := by sorry
