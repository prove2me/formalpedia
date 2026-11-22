-- Prove2me | Theorems.Thm_OrderClosures_gaoIterationTower_strict
-- name    : OrderClosures.gaoIterationTower_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:21.729607+00:00
-- url     : https://prove2.me/theorems/55f3b025-9f2d-4ded-a92e-e5d8a71b26f1
-- title:
--   Order Closures: gao Iteration Tower strict
-- statement:
--   Transfers strictness from a suitable Gao component to every stage below
--   the target ordinal of the global iteration tower.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L477-L526
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L477-L526

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.gaoIterationTower_strict
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    ∀ η < Ordinal.lift.{u + 1, u} (Cardinal.ord (Order.succ κ)),
      (canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage η ⊂
        (canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage (Order.succ η) := by sorry
