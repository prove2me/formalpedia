-- Prove2me | Theorems.Thm_HajnalSzemeredi_hajnalSzemeredi_exact
-- name    : HajnalSzemeredi.hajnalSzemeredi_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:51.132812+00:00
-- url     : https://prove2.me/theorems/6daa9ce5-d716-4174-9fee-369c517cb354
-- title:
--   Hajnal Szemeredi: hajnal Szemeredi exact
-- statement:
--   Forma exacta.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Final.lean#L44-L55
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Final.lean#L44-L55

module
public import Definitions.Def_HajnalSzemeredi_Main
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_HajnalSzemeredi_Final
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset
open HajnalSzemeredi
variable {V : Type*} [Fintype V]

theorem HajnalSzemeredi.hajnalSzemeredi_exact (G : SimpleGraph V) [DecidableRel G.Adj] (r s : ℕ)
    (hcard : Fintype.card V = s * (r + 1)) (h : ∀ v, G.degree v ≤ r) :
    ∃ C : G.Coloring (Fin (r + 1)), ∀ i, (univ.filter fun v => C v = i).card = s := by sorry
