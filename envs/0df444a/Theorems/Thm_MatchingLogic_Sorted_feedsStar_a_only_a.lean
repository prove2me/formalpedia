-- Prove2me | Theorems.Thm_MatchingLogic_Sorted_feedsStar_a_only_a
-- name    : MatchingLogic.Sorted.feedsStar_a_only_a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:27.570926+00:00
-- url     : https://prove2.me/theorems/3340faf4-75ce-42f2-b78c-007c6caf80c1
-- title:
--   Sorted: feeds Star a only a
-- statement:
--   **In `S3`, sort `a` feeds only itself**, because no symbol has an argument
--   of sort `a`.  This is the structural fact the whole argument rests on.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SortedProof.lean#L186-L194
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SortedProof.lean#L186-L194

module
public import Definitions.Def_LeanPool_MatchingLogic_Sorted
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_SortedProof
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Sorted
variable {S : MSignature} {Var : Type} [DecidableEq S.Srt] [DecidableEq Var]

theorem MatchingLogic.Sorted.feedsStar_a_only_a (t : Srt3) : FeedsStar S3 Srt3.a t → t = Srt3.a := by sorry
