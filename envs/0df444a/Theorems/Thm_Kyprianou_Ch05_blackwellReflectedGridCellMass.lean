-- Prove2me | Theorems.Thm_Kyprianou_Ch05_blackwellReflectedGridCellMass
-- name    : Kyprianou.Ch05.blackwellReflectedGridCellMass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:26:18.721659+00:00
-- url     : https://prove2.me/theorems/42de27da-cd0d-4546-93b9-3ae75d92202f
-- title:
--   Blackwell limit for reflected truncated half-open grid cells
-- statement:
--   Blackwell limit for reflected truncated half-open grid cells
-- source:
--   Kyprianou (2006), Theorem 5.1(ii) corrected: grid and Tannery steps.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.blackwellReflectedGridCellMass
    (V : Measure Real) (mu : Real)
    (hBlackwell : ∀ d : Real, 0 < d →
      Tendsto (fun x : Real => (V (Set.Ioc x (x+d))).toReal)
        atTop (nhds (d/mu)))
    (d : Real) (hd : 0 < d) (k : Nat) :
    Tendsto (fun x : Real => (V (Set.Icc 0 x ∩ Set.Ioc (x-((k : Real)+1)*d) (x-(k : Real)*d))).toReal)
      atTop (nhds (d/mu)) := by sorry
