-- Prove2me | Theorems.Thm_MatchingLogic_Sorted_mprovable_empty_of_not_feeds
-- name    : MatchingLogic.Sorted.mprovable_empty_of_not_feeds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:32.384939+00:00
-- url     : https://prove2.me/theorems/094333bd-1129-4934-b6d6-c03cd0ea94bb
-- title:
--   Sorted: mprovable empty of not feeds
-- statement:
--   Every line of a derivation whose sort does not feed back to `sΓ` is
--   derivable from the axioms alone: a hypothesis line has sort `sΓ`, and no rule
--   carries an `sΓ` premise into a conclusion of a sort that `sΓ` does not feed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SortedProof.lean#L215-L257
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SortedProof.lean#L215-L257

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

theorem MatchingLogic.Sorted.mprovable_empty_of_not_feeds {sΓ s : S.Srt}
    (Γ : Set (MPattern S Var sΓ)) (φ : MPattern S Var s)
    (hfeed : ¬ FeedsStar S sΓ s) (h : MProvable Γ φ) :
    MProvable (∅ : Set (MPattern S Var sΓ)) φ := by sorry
