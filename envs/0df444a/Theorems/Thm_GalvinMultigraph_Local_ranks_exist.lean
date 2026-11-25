-- Prove2me | Theorems.Thm_GalvinMultigraph_Local_ranks_exist
-- name    : GalvinMultigraph.Local.ranks_exist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:28:51.314047+00:00
-- url     : https://prove2.me/theorems/2bb1075c-550c-4eae-a847-974a8db33c31
-- title:
--   Local: ranks exist
-- statement:
--   **The rank construction.**  Each left vertex `u` is given a starting position `aL u` and each
--   right vertex `v` a starting position `aR v`.  Under the two displayed hypotheses — the bottoms and
--   the tops of the two position intervals of every edge are related by the edge constant `c e` — the
--   edges of `S` can be numbered at each vertex, consecutively from the starting position, so that for
--   every edge `e = uv` the position of `e` at `v` exceeds its position at `u` by at most `c e`.
--
--   Applied with `aL = aR = 0` and `c e = max (d u) (d v) - d u` this is exactly the ordering needed
--   for the Galvin orientation in the Borodin–Kostochka–Woodall theorem.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L297-L535
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Local/Ranks.lean#L297-L535

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
omit [Fintype R] [Fintype E]

theorem GalvinMultigraph.Local.ranks_exist (left : E → U) (right : E → R) (c : E → ℕ) (S : Finset E) :
    ∀ aL : U → ℕ, ∀ aR : R → ℕ,
    (∀ e ∈ S, aR (right e) ≤ aL (left e) + c e) →
    (∀ e ∈ S, aR (right e) + degROn right S (right e)
        ≤ aL (left e) + degLOn left S (left e) + c e) →
    ∃ pL pR : E → ℕ,
      (∀ e ∈ S, aL (left e) ≤ pL e ∧ pL e < aL (left e) + degLOn left S (left e)) ∧
      (∀ e ∈ S, aR (right e) ≤ pR e ∧ pR e < aR (right e) + degROn right S (right e)) ∧
      (∀ e ∈ S, ∀ f ∈ S, left e = left f → pL e = pL f → e = f) ∧
      (∀ e ∈ S, ∀ f ∈ S, right e = right f → pR e = pR f → e = f) ∧
      (∀ e ∈ S, pR e ≤ pL e + c e) := by sorry
