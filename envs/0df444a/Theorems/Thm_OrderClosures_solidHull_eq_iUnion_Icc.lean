-- Prove2me | Theorems.Thm_OrderClosures_solidHull_eq_iUnion_Icc
-- name    : OrderClosures.solidHull_eq_iUnion_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:36.869877+00:00
-- url     : https://prove2.me/theorems/86ee3457-6f80-4c4b-a795-398f6a7e0535
-- title:
--   Order Closures: solid Hull eq i Union Icc
-- statement:
--   The interval-union description of the solid hull used in the paper.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/OrderAdherence.lean#L356-L368
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/OrderAdherence.lean#L356-L368

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Pi
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LatticeSeminorm
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Tactic_LLexpr
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Examples_CofK_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Hom
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
set_option autoImplicit true
@[expose] public section
public section
open Set
open OrderClosures
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem OrderClosures.solidHull_eq_iUnion_Icc (A : Set X) :
    solidHull A = ⋃ a ∈ A, Set.Icc (-|a|) |a| := by sorry
