-- Prove2me | Theorems.Thm_MeasureTheory_map_curryProd_pi
-- name    : MeasureTheory.map_curryProd_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:33.014862+00:00
-- url     : https://prove2.me/theorems/bc6dd162-b71c-457b-9a7b-b49ad340e1bc
-- title:
--   Measure Theory: map curry Prod pi
-- statement:
--   **Currying a product index preserves `Measure.pi`.** The plain currying map
--   `y ↦ fun i j => y (i, j)` pushes the product measure over `ιp × κp` forward to the
--   iterated product measure.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/MeasureTheory/PiCurry.lean#L37-L74
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/MeasureTheory/PiCurry.lean#L37-L74

module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Definitions.Def_BornVolumeLean_MeasureTheory_PiCurry
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory
variable {ιp κp : Type*} [Fintype ιp] [Fintype κp] {α : ιp × κp → Type*}
  [∀ p, MeasurableSpace (α p)] (ν : (p : ιp × κp) → Measure (α p)) [∀ p, SigmaFinite (ν p)]

theorem MeasureTheory.map_curryProd_pi :
    Measure.map (fun y : (p : ιp × κp) → α p => fun i j => y (i, j)) (Measure.pi ν)
      = Measure.pi (fun i => Measure.pi (fun j => ν (i, j))) := by sorry
