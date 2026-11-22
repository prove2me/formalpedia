-- Prove2me | Theorems.Thm_OrderClosures_booleanStoneClopen_sSup
-- name    : OrderClosures.booleanStoneClopen_sSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:33.794628+00:00
-- url     : https://prove2.me/theorems/b59f25ba-9be0-41be-96a0-a31b75f4f831
-- title:
--   Order Closures: boolean Stone Clopen s Sup
-- statement:
--   Shows that arbitrary Boolean suprema correspond to closures of unions of
--   Stone clopens; used to transfer completeness into vector sublattices.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1176-L1206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1176-L1206

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
variable (B : Type u) [CompleteBooleanAlgebra B]

theorem OrderClosures.booleanStoneClopen_sSup (S : Set B) :
    booleanStoneClopen B (sSup S) =
      closure (⋃ b ∈ S, booleanStoneClopen B b) := by sorry
