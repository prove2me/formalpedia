-- Prove2me | Theorems.Thm_Kyprianou_Ch05_blackwellGridWeightedTannery
-- name    : Kyprianou.Ch05.blackwellGridWeightedTannery
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:26:11.621014+00:00
-- url     : https://prove2.me/theorems/b569a454-a434-402b-a11f-1c8f12ca93c2
-- title:
--   Summable weighted reflected grid masses converge by Tannery
-- statement:
--   Summable weighted reflected grid masses converge by Tannery
-- source:
--   Kyprianou (2006), Theorem 5.1(ii) corrected: grid and Tannery steps.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.blackwellGridWeightedTannery
    (V : Measure Real) (mu : Real)
    (hBlackwell : ∀ d : Real, 0 < d →
      Tendsto (fun x : Real => (V (Set.Ioc x (x+d))).toReal)
        atTop (nhds (d/mu)))
    (d : Real) (hd : 0 < d)
    (C : ENNReal) (hC : C ≠ ⊤)
    (hbound : ∀ a x : Real, V (Set.Icc 0 x ∩ Set.Ioc a (a+d)) ≤ C)
    (c : Nat → Real) (hs : Summable (fun k => |c k|)) :
    Tendsto (fun x : Real => ∑' k : Nat, c k * (V (Set.Icc 0 x ∩ Set.Ioc (x-((k : Real)+1)*d) (x-(k : Real)*d))).toReal)
      atTop (nhds ((∑' k : Nat, c k) * (d/mu))) := by sorry
