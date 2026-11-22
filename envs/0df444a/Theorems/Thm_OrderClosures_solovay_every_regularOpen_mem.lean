-- Prove2me | Theorems.Thm_OrderClosures_solovay_every_regularOpen_mem
-- name    : OrderClosures.solovay_every_regularOpen_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:21.903794+00:00
-- url     : https://prove2.me/theorems/67586499-e9c0-480b-9cdb-329ae90eb708
-- title:
--   Order Closures: solovay every regular Open mem
-- statement:
--   Shows every regular open element belongs to any complete subalgebra
--   containing the Solovay generators; this proves generation of the full algebra.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L546-L556
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L546-L556

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
omit [LinearOrder Gamma]

theorem OrderClosures.solovay_every_regularOpen_mem
    (L : BooleanSubalgebra (RegularOpen (SolovayProduct Gamma)))
    (hcomplete : IsCompleteBooleanSubalgebra L)
    (hA : ∀ n eta, solovayA Gamma n eta ∈ L)
    (U : RegularOpen (SolovayProduct Gamma)) : U ∈ L := by sorry
