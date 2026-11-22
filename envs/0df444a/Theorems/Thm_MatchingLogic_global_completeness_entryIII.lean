-- Prove2me | Theorems.Thm_MatchingLogic_global_completeness_entryIII
-- name    : MatchingLogic.global_completeness_entryIII
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:40:13.028506+00:00
-- url     : https://prove2.me/theorems/ed314da3-0cb7-4b70-b691-41e39bdd6acd
-- title:
--   Matching Logic: global completeness entry III
-- statement:
--   The one-sorted case of Corollary 15 with both soundness and strong local
--   completeness supplied by the development.  Only the paper's closedness premises
--   remain.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Conclusion.lean#L67-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Conclusion.lean#L67-L72

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
public import Mathlib.Logic.Denumerable
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalConstruction
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_ModelExistence
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Renaming
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_SignatureReduction
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Conclusion
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature}

theorem MatchingLogic.global_completeness_entryIII {Var : Type}
    [DecidableEq Var] [Denumerable Var]
    {Gamma : Set (Pattern S Var)} {phi : Pattern S Var}
    (hGamma : ∀ gamma ∈ Gamma, Closed gamma) (hphi : Closed phi) :
    GlobalCons Gamma phi ↔ Provable Gamma phi := by sorry
