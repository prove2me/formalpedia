-- Prove2me | Theorems.Thm_OrderClosures_cnfValue_add_singleton_below
-- name    : OrderClosures.cnfValue_add_singleton_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:15.188509+00:00
-- url     : https://prove2.me/theorems/0f591d64-87f0-4f23-9e97-f927c01efb50
-- title:
--   Order Closures: cnf Value add singleton below
-- statement:
--   Appending a smaller singleton CNF term to a finite prefix computes its normal form.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L292-L363
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L292-L363

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.cnfValue_add_singleton_below
    (pre : List (Ordinal.{u} × Ordinal.{u})) (γ : Ordinal.{u}) (n : ℕ)
    (hpreSorted : (pre.map Prod.fst).Pairwise (fun x y ↦ y < x))
    (hpreAbove : ∀ x ∈ pre, γ < x.1)
    (hprePos : ∀ x ∈ pre, 0 < x.2)
    (hpreLt : ∀ x ∈ pre, x.2 < Ordinal.omega0)
    (q : Ordinal.{u}) (hq : q ∈ singletonCNFBelow γ) :
    ∃ δ d, Ordinal.CNF Ordinal.omega0 q = [(δ, d)] ∧ δ < γ ∧
      Ordinal.CNF Ordinal.omega0
        (cnfValue pre + Ordinal.omega0 ^ γ * (n : Ordinal) + q) =
        if n = 0 then pre ++ [(δ, d)]
        else pre ++ (γ, (n : Ordinal)) :: [(δ, d)] := by sorry
