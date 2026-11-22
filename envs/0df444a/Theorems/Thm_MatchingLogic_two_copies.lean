-- Prove2me | Theorems.Thm_MatchingLogic_two_copies
-- name    : MatchingLogic.two_copies
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:29.792373+00:00
-- url     : https://prove2.me/theorems/4cf7e11b-3d0f-4f1d-9f4b-fcf863a87e56
-- title:
--   Matching Logic: two copies
-- statement:
--   **Lemma 11 (two copies)**, in membership form.  Equivalent to the display in
--   the paper (see `two_copies_set`); this form is the one to prove by induction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/DoubleCover.lean#L81-L184
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/DoubleCover.lean#L81-L184

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

theorem MatchingLogic.two_copies (hC : M.BackwardClosed C) (hne : C.Nonempty)
    (star : M.carrier) (hstar : star ∉ C)
    (ψ : Pattern S Var) (ν : Var → (C × Bool)) (p : C × Bool) :
    p ∈ (cover M C hne).denote ν ψ ↔
      (p.1 : M.carrier) ∈ M.denote (fun x => proj M C star p.2 (ν x)) ψ := by sorry
