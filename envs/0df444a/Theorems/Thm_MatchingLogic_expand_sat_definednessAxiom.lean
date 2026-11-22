-- Prove2me | Theorems.Thm_MatchingLogic_expand_sat_definednessAxiom
-- name    : MatchingLogic.expand_sat_definednessAxiom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:05.582178+00:00
-- url     : https://prove2.me/theorems/b8ca9bdd-022c-4121-975c-732fe2bb5053
-- title:
--   Matching Logic: expand sat definedness Axiom
-- statement:
--   The expansion satisfies the definedness axiom, so it really is a model of
--   `Γ ∪ {⌈x⌉}` whenever `M` is a model of `Γ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Definedness.lean#L119-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Definedness.lean#L119-L126

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

theorem MatchingLogic.expand_sat_definednessAxiom (M : Model S) (x : Var) :
    (expand M).Sat (definednessAxiom (S := S) x) := by sorry
