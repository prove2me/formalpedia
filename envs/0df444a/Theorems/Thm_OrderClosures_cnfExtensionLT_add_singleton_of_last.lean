-- Prove2me | Theorems.Thm_OrderClosures_cnfExtensionLT_add_singleton_of_last
-- name    : OrderClosures.cnfExtensionLT_add_singleton_of_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:33.693832+00:00
-- url     : https://prove2.me/theorems/391e3d51-dc04-47e0-9012-1a41867f0058
-- title:
--   Order Closures: cnf Extension LT add singleton of last
-- statement:
--   Appending one smaller singleton monomial creates a strict CNF extension;
--   used in the later Gao-stage approximation argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L485-L519
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L485-L519

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

theorem OrderClosures.cnfExtensionLT_add_singleton_of_last
    {ζ q γ d β c : Ordinal.{u}}
    {pre : List (Ordinal.{u} × Ordinal.{u})}
    (hζ : Ordinal.CNF Ordinal.omega0 ζ = pre ++ [(β, c)])
    (hq : Ordinal.CNF Ordinal.omega0 q = [(γ, d)])
    (hβγ : β ≤ γ) : cnfExtensionLT ζ (ζ + q) := by sorry
