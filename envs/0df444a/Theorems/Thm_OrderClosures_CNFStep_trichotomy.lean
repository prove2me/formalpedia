-- Prove2me | Theorems.Thm_OrderClosures_CNFStep_trichotomy
-- name    : OrderClosures.CNFStep.trichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:26.895807+00:00
-- url     : https://prove2.me/theorems/5d1289c1-ed02-4caf-ad1e-f2603ed8a632
-- title:
--   CNFStep: trichotomy
-- statement:
--   Establishes comparability of two one-step extensions above a common
--   prefix; used to linearize each upper cone.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L537-L560
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L537-L560

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.CNFStep.trichotomy {pre : List (Ordinal.{u} × Ordinal.{u})}
    {x y z : Ordinal.{u} × Ordinal.{u}}
    (hxy : CNFStep pre x y) (hxz : CNFStep pre x z) :
    y = z ∨ CNFStep pre y z ∨ CNFStep pre z y := by sorry
