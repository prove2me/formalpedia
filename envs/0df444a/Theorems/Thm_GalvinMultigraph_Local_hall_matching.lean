-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_hall_matching
-- name    : GalvinMultigraph.Local.hall_matching
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:28:14.43947+00:00
-- url     : https://prove2.me/theorems/381d9664-6c7b-41c4-a0a3-b2dcc9cf3b67
-- title:
--   Local: hall matching
-- statement:
--   Hall's theorem, in the form used below: if every subset of `A` has at least as many
--   neighbours as elements, then `S` contains a matching covering `A` on the left and nothing else,
--   whose right endpoints exhaust `A`'s neighbourhood as far as cardinality permits.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L146-L210
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L146-L210

module
public import Definitions.Def_GalvinMultigraph_Local_Konig
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Set
public import Definitions.Def_GalvinMultigraph_Local_Ranks
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
open GalvinMultigraph GalvinMultigraph.Local
variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E]
  [DecidableEq U] [DecidableEq R] [DecidableEq E]
omit [Fintype U] [Fintype R] [Fintype E]

theorem GalvinMultigraph.Local.hall_matching (left : E → U) (right : E → R) (S : Finset E) (A : Finset U)
    (hAne : A.Nonempty)
    (hall : ∀ B ⊆ A,
      B.card ≤ (B.biUnion (fun u => (S.filter fun e => left e = u).image right)).card) :
    ∃ M : Finset E, M ⊆ S ∧ M.Nonempty ∧ IsMatchingOn left right M ∧
      (∀ u ∈ A, ∃ e ∈ M, left e = u) ∧ (∀ e ∈ M, left e ∈ A) ∧
      M.image right ⊆ A.biUnion (fun u => (S.filter fun e => left e = u).image right) ∧
      A.card ≤ (M.image right).card := by sorry
