-- Prove2me | Theorems.Thm_OrderClosures_continuousMap_exists_finite_coordinates
-- name    : OrderClosures.continuousMap_exists_finite_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:45.349771+00:00
-- url     : https://prove2.me/theorems/94cd4441-e94c-4a9d-8dd3-122c4da78b07
-- title:
--   Order Closures: continuous Map exists finite coordinates
-- statement:
--   Extracts finitely many Cantor-cube coordinates controlling a continuous
--   real map; used to prove the incomparable-projection infimum formula.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L46-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L46-L65

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.continuousMap_exists_finite_coordinates
    {I : Type u} {K : Set (I → Bool)} (f : C(K, ℝ)) (x : K)
    {V : Set ℝ} (hV : IsOpen V) (hxV : f x ∈ V) :
    ∃ F : Finset I, ∀ y : K, (∀ i ∈ F, y.1 i = x.1 i) → f y ∈ V := by sorry
