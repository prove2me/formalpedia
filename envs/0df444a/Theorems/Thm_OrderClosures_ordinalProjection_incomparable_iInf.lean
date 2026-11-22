-- Prove2me | Theorems.Thm_OrderClosures_ordinalProjection_incomparable_iInf
-- name    : OrderClosures.ordinalProjection_incomparable_iInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:52.727714+00:00
-- url     : https://prove2.me/theorems/35fac5d7-625b-4a03-9271-b4c599aea2a3
-- title:
--   Order Closures: ordinal Projection incomparable i Inf
-- statement:
--   Claim 1 in the proof of Theorem `thm:solid-iterations`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L89-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L89-L164

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.ordinalProjection_incomparable_iInf
    (ξ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (hZ : Z.Infinite)
    (hinc : Z.Pairwise fun ζ ζ' ↦ ¬ cnfExtensionLE ζ.1 ζ'.1) :
    IsGLB (ordinalProjection ξ '' Z) 0 := by sorry
