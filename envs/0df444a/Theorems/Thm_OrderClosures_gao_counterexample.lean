-- Prove2me | Theorems.Thm_OrderClosures_gao_counterexample
-- name    : OrderClosures.gao_counterexample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:08:32.041343+00:00
-- url     : https://prove2.me/theorems/76344bc8-1411-4da8-bb69-b572c98e178c
-- title:
--   Order Closures: gao counterexample
-- statement:
--   Paper Proposition 2.1: an order-complete `C(K)` of arbitrarily large density,
--   with a closed separable sublattice whose only order-closed vector-sublattice
--   extension is all of `C(K)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Counterexample.lean#L45-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Counterexample.lean#L45-L74

module
public import Mathlib.Data.Fintype.Order
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungCharacterization
public import Mathlib.Order.TransfiniteIteration
public import Mathlib.SetTheory.Ordinal.CantorNormalForm
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.gao_counterexample (κ : Cardinal.{u}) :
    ∃ (K : Type u) (_ : TopologicalSpace K) (_ : CompactSpace K) (_ : T2Space K),
      IsOrderComplete C(K, ℝ) ∧ κ ≤ densityCharacter C(K, ℝ) ∧
      ∃ Y : VectorSublattice C(K, ℝ),
        IsClosed (Y : Set C(K, ℝ)) ∧
          TopologicalSpace.IsSeparable (Y : Set C(K, ℝ)) ∧
          ∀ Z : VectorSublattice C(K, ℝ),
            Y ≤ Z → IsOrderClosed (Z : Set C(K, ℝ)) → Z = ⊤ := by sorry
