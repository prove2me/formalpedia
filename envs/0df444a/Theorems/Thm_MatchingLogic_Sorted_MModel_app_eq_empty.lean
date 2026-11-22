-- Prove2me | Theorems.Thm_MatchingLogic_Sorted_MModel_app_eq_empty
-- name    : MatchingLogic.Sorted.MModel.app_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:27.722953+00:00
-- url     : https://prove2.me/theorems/530f0c9e-8ba8-4e36-905a-2f008507fa8d
-- title:
--   MModel: app eq empty
-- statement:
--   A many-sorted symbol application is empty if one argument is empty.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Sorted.lean#L144-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Sorted.lean#L144-L152

module
public import Aesop.BuiltinRules
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Sorted
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Sorted
variable {S : MSignature} {Var : Type}

theorem MatchingLogic.Sorted.MModel.app_eq_empty (M : MModel S) (σ : S.Sym)
    (A : (i : Fin (S.arity σ)) → Set (M.carrier (S.argSort σ i)))
    (i : Fin (S.arity σ)) (h : A i = ∅) : M.app σ A = ∅ := by sorry
