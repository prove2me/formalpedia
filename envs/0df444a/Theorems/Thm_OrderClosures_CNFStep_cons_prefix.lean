-- Prove2me | Theorems.Thm_OrderClosures_CNFStep_cons_prefix
-- name    : OrderClosures.CNFStep.cons_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:18.304888+00:00
-- url     : https://prove2.me/theorems/799d9625-9603-4f3c-83f2-1843e14bf4bd
-- title:
--   CNFStep: cons prefix
-- statement:
--   Adds a common head to a one-step CNF extension; used to lift extensions
--   through arbitrary common prefixes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L324-L337
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L324-L337

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

theorem OrderClosures.CNFStep.cons_prefix
    {pre : List (Ordinal.{u} × Ordinal.{u})}
    {x y : Ordinal.{u} × Ordinal.{u}} {δ e : Ordinal.{u}}
    (h : CNFStep pre x y) (hy : y.1 < δ) :
    CNFStep ((δ, e) :: pre) x y := by sorry
