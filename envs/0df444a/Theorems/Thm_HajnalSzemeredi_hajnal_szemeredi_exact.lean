-- Prove2me | Theorems.Thm_HajnalSzemeredi_hajnal_szemeredi_exact
-- name    : HajnalSzemeredi.hajnal_szemeredi_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:08:05.075799+00:00
-- url     : https://prove2.me/theorems/c3350546-f97a-57b5-b902-64654c4b7201
-- title:
--   Hajnal Szemeredi: hajnal szemeredi exact
-- statement:
--   The Hajnal Szemeredi construction uses the hajnal szemeredi exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/Solution.lean#L32-L37
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/Solution.lean#L32-L37

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_HajnalSzemeredi
public import Definitions.Def_HajnalSzemeredi_Solution
set_option autoImplicit true
@[expose] public section
public section
open HajnalSzemeredi

theorem HajnalSzemeredi.hajnal_szemeredi_exact {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hcard : Fintype.card V = s * (r + 1)) (h : ∀ v, G.degree v ≤ r) :
    ∃ C : G.Coloring (Fin (r + 1)), ∀ i : Fin (r + 1),
      (Finset.univ.filter fun v => C v = i).card = s := by sorry
