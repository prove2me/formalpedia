-- Prove2me | Theorems.Thm_OrderClosures_booleanStoneClopen_injective
-- name    : OrderClosures.booleanStoneClopen_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:20.266244+00:00
-- url     : https://prove2.me/theorems/d673ec85-defc-4f1f-928f-2b62a99608da
-- title:
--   Order Closures: boolean Stone Clopen injective
-- statement:
--   Proves injectivity of the Stone clopen representation; used to embed the
--   complete Boolean algebra into continuous functions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L744-L749
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L744-L749

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
variable (B : Type u) [BooleanAlgebra B]

theorem OrderClosures.booleanStoneClopen_injective :
    Function.Injective (booleanStoneClopen B) := by sorry
