-- Prove2me | Theorems.Thm_OrderClosures_regularOpenOfClopen_compl
-- name    : OrderClosures.regularOpenOfClopen_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:23.308837+00:00
-- url     : https://prove2.me/theorems/e2418a60-4085-4c67-bad4-395be4759517
-- title:
--   Order Closures: regular Open Of Clopen compl
-- statement:
--   Computes complements of clopen sets inside the regular-open algebra;
--   used to show the cylinder-generated family is a Boolean subalgebra.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L106-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L106-L126

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

theorem OrderClosures.regularOpenOfClopen_compl {X : Type u} [TopologicalSpace X]
    (s : Set X) (hs : IsClopen s) :
    regularOpenOfClopen sᶜ hs.compl = (regularOpenOfClopen s hs)ᶜ := by sorry
