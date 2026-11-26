-- Prove2me | Theorems.Thm_HajnalSzemeredi_hajnal_szemeredi
-- name    : HajnalSzemeredi.hajnal_szemeredi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:08:13.393082+00:00
-- url     : https://prove2.me/theorems/cad1ef54-883a-4aaf-b515-bd7b993d4bcb
-- title:
--   Hajnal Szemeredi: hajnal szemeredi
-- statement:
--   The Hajnal Szemeredi construction uses the hajnal szemeredi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/Solution.lean#L24-L30
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/Solution.lean#L24-L30

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_HajnalSzemeredi
public import Definitions.Def_HajnalSzemeredi_Solution
set_option autoImplicit true
@[expose] public section
public section
open HajnalSzemeredi

theorem HajnalSzemeredi.hajnal_szemeredi {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (h : ∀ v, G.degree v ≤ r) :
    ∃ C : G.Coloring (Fin (r + 1)), ∀ i j : Fin (r + 1),
      (Finset.univ.filter fun v => C v = i).card ≤
        (Finset.univ.filter fun v => C v = j).card + 1 := by sorry
