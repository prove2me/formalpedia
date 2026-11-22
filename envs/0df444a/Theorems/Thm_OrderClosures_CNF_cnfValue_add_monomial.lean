-- Prove2me | Theorems.Thm_OrderClosures_CNF_cnfValue_add_monomial
-- name    : OrderClosures.CNF_cnfValue_add_monomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:21.315906+00:00
-- url     : https://prove2.me/theorems/1d5d8a89-aa8c-4543-abc4-84f01547b63d
-- title:
--   Order Closures: CNF cnf Value add monomial
-- statement:
--   Identifies the canonical CNF of a value with one added monomial; used to
--   construct explicit CNF extensions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L309-L320
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L309-L320

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

theorem OrderClosures.CNF_cnfValue_add_monomial
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hpos : ∀ p ∈ l, 0 < p.2)
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0)
    (γ d : Ordinal.{u}) (hdpos : 0 < d) (hdlt : d < Ordinal.omega0) :
    Ordinal.CNF Ordinal.omega0
      (cnfValue l + Ordinal.omega0 ^ γ * d) = cnfAddMonomial l γ d := by sorry
