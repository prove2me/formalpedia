-- Prove2me | Theorems.Thm_OrderClosures_solovayBad_eq
-- name    : OrderClosures.solovayBad_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:08.774071+00:00
-- url     : https://prove2.me/theorems/0495b615-5759-43d0-a576-05c38e5e76eb
-- title:
--   Order Closures: solovay Bad eq
-- statement:
--   Decomposes the exceptional comparison event into previously generated
--   pieces; used in the induction recovering cylinder elements.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L345-L351
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L345-L351

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

theorem OrderClosures.solovayBad_eq (m n : ℕ) (eta : Gamma) :
    solovayBad Gamma m n eta =
      solovayStrict Gamma m n ⊓ solovayNotLT Gamma m eta := by sorry
