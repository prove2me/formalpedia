-- Prove2me | Theorems.Thm_MatchingLogic_localize_not_redundant
-- name    : MatchingLogic.localize_not_redundant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:32:37.253685+00:00
-- url     : https://prove2.me/theorems/6e13e561-05bc-4e36-80b9-4916ea852dad
-- title:
--   Matching Logic: localize not redundant
-- statement:
--   **Replacing `Δ_Γ` by `Γ` makes Theorem 13 false**, even for closed `Γ` and
--   closed `φ`.  So the localization in `semantic_localization` is load-bearing and
--   the theorem forbids something.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Independence.lean#L124-L214
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Independence.lean#L124-L214

module
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Independence
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.localize_not_redundant :
    ¬ (∀ (S : Signature) (Var : Type) (_ : DecidableEq Var)
         (Γ : Set (Pattern S Var)) (φ : Pattern S Var),
         (∀ γ ∈ Γ, Closed γ) → Closed φ →
         (GlobalCons Γ φ ↔ LocalCons Γ φ)) := by sorry
