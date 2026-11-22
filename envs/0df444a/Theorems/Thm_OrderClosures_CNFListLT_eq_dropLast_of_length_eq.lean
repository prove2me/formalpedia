-- Prove2me | Theorems.Thm_OrderClosures_CNFListLT_eq_dropLast_of_length_eq
-- name    : OrderClosures.CNFListLT.eq_dropLast_of_length_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:59.702646+00:00
-- url     : https://prove2.me/theorems/180e13d7-0945-492f-9fcc-65202fe478f6
-- title:
--   CNFList LT: eq drop Last of length eq
-- statement:
--   Identifies an equal-length CNF extension as deletion of the last source
--   term; used to analyze stabilization in chains of extensions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L410-L425
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L410-L425

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.CNFListLT.eq_dropLast_of_length_eq
    {l m : List (Ordinal.{u} × Ordinal.{u})}
    (h : CNFListLT l m) (hlen : m.length = l.length) :
    ∃ x y, l = l.dropLast ++ [x] ∧ m = l.dropLast ++ [y] ∧
      CNFStep l.dropLast x y := by sorry
