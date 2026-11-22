-- Prove2me | Theorems.Thm_OrderClosures_cardinalMk_le_densityCharacter_of_oneSeparated
-- name    : OrderClosures.cardinalMk_le_densityCharacter_of_oneSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:57.8742+00:00
-- url     : https://prove2.me/theorems/f2f5a377-4ae7-4e37-97c8-ce2d23697c7d
-- title:
--   Order Closures: cardinal Mk le density Character of one Separated
-- statement:
--   Bounds density character below by the cardinality of a one-separated
--   family; used for the Stone-space continuous-function density estimate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1504-L1529
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1504-L1529

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

theorem OrderClosures.cardinalMk_le_densityCharacter_of_oneSeparated
    {A : Type u} {X : Type u} [PseudoMetricSpace X]
    (e : A → X) (hsep : ∀ a b, a ≠ b → (1 : ℝ) ≤ dist (e a) (e b)) :
    Cardinal.mk A ≤ densityCharacter X := by sorry
