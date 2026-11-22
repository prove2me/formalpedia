-- Prove2me | Theorems.Thm_MatchingLogic_two_copies_set
-- name    : MatchingLogic.two_copies_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:44.815469+00:00
-- url     : https://prove2.me/theorems/a37dd591-b975-4231-9d7c-224b3b34588e
-- title:
--   Matching Logic: two copies set
-- statement:
--   **Lemma 11 (two copies)**, in the paper's displayed set form:
--   `ν(ψ)_N = (π₀(ν)(ψ)_M ∩ C) × {0} ∪ (π₁(ν)(ψ)_M ∩ C) × {1}`.
--   The `∩ C` is absorbed by the subtype `↥C`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/DoubleCover.lean#L189-L221
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/DoubleCover.lean#L189-L221

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_DoubleCover
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
variable (M : Model S) (C : Set M.carrier)

theorem MatchingLogic.two_copies_set (hC : M.BackwardClosed C) (hne : C.Nonempty)
    (star : M.carrier) (hstar : star ∉ C)
    (ψ : Pattern S Var) (ν : Var → (C × Bool)) :
    (cover M C hne).denote ν ψ =
      {p : C × Bool | p.2 = false ∧
        (p.1 : M.carrier) ∈ M.denote (fun x => proj M C star false (ν x)) ψ} ∪
      {p : C × Bool | p.2 = true ∧
        (p.1 : M.carrier) ∈ M.denote (fun x => proj M C star true (ν x)) ψ} := by sorry
