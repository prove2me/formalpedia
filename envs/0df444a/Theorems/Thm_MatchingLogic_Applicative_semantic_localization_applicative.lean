-- Prove2me | Theorems.Thm_MatchingLogic_Applicative_semantic_localization_applicative
-- name    : MatchingLogic.Applicative.semantic_localization_applicative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:58.036806+00:00
-- url     : https://prove2.me/theorems/515d9a23-5ab6-4d7a-a45a-61c71c80bb98
-- title:
--   Applicative: semantic localization applicative
-- statement:
--   **"Everything above applies unchanged."**  Theorem 13 for applicative
--   matching logic, by instantiation and nothing else.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Applicative.lean#L134-L138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Applicative.lean#L134-L138

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Composite
public import Definitions.Def_LeanPool_MatchingLogic_Applicative
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Applicative
variable {Const : Type} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.Applicative.semantic_localization_applicative
    {Γ : Set (Pattern (appSig Const) Var)} {φ : Pattern (appSig Const) Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (hφ : Closed φ) :
    GlobalCons Γ φ ↔ LocalCons (localize Γ) φ := by sorry
