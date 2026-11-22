-- Prove2me | Theorems.Thm_MatchingLogic_denote_emb
-- name    : MatchingLogic.denote_emb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:33.069901+00:00
-- url     : https://prove2.me/theorems/ce25589d-cffa-4cae-b276-d9b833e58ea2
-- title:
--   Matching Logic: denote emb
-- statement:
--   The embedding preserves denotation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Definedness.lean#L84-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Definedness.lean#L84-L115

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Definedness
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.denote_emb (M : Model S) (ρ : Var → M.carrier) (φ : Pattern S Var) :
    (expand M).denote ρ (emb φ) = M.denote ρ φ := by sorry
