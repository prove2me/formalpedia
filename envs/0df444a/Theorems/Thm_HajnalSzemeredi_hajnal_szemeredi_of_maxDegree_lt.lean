-- Prove2me | Theorems.Thm_HajnalSzemeredi_hajnal_szemeredi_of_maxDegree_lt
-- name    : HajnalSzemeredi.hajnal_szemeredi_of_maxDegree_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:08:24.811303+00:00
-- url     : https://prove2.me/theorems/a6c23e23-ab33-4673-8a88-43799adb8ce1
-- title:
--   Hajnal Szemeredi: hajnal szemeredi of max Degree lt
-- statement:
--   The Hajnal Szemeredi construction uses the hajnal szemeredi of max Degree lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/Solution.lean#L39-L45
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/Solution.lean#L39-L45

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_HajnalSzemeredi
public import Definitions.Def_HajnalSzemeredi_Solution
set_option autoImplicit true
@[expose] public section
public section
open HajnalSzemeredi

theorem HajnalSzemeredi.hajnal_szemeredi_of_maxDegree_lt {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hk : G.maxDegree < k) :
    ∃ C : G.Coloring (Fin k), ∀ i j : Fin k,
      (Finset.univ.filter fun v => C v = i).card ≤
        (Finset.univ.filter fun v => C v = j).card + 1 := by sorry
