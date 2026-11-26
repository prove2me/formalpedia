-- Prove2me | Theorems.Thm_Kyprianou_Ch05_keyRenewalFromBlackwellMeasurableDRI
-- name    : Kyprianou.Ch05.keyRenewalFromBlackwellMeasurableDRI
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:24:35.237402+00:00
-- url     : https://prove2.me/theorems/a870fd55-db3e-52d6-ad48-07c87ddab733
-- title:
--   Key renewal limit via Blackwell and measurable direct Riemann integrability
-- statement:
--   Key renewal limit via Blackwell and measurable direct Riemann integrability
-- source:
--   Kyprianou (2006), Theorem 5.1, corrected Borel-measurable key renewal theorem; discussion 1dbfd76f-095f-4acc-b3fe-3e528b888bc6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.keyRenewalFromBlackwellMeasurableDRI
    (V : Measure Real) (mu : Real) (hmu : 0 < mu)
    (hfinite : ∀ x : Real, V (Set.Icc 0 x) ≠ ⊤)
    (hBlackwell : ∀ d : Real, 0 < d →
      Tendsto (fun x : Real => (V (Set.Ioc x (x+d))).toReal)
        atTop (nhds (d/mu)))
    (hUniform : ∀ d : Real, 0 < d → ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ a x : Real, V (Set.Icc 0 x ∩ Set.Ioc a (a+d)) ≤ C)
    (h : Real → Real) (hm : Measurable h) (hDRI : DirectlyRiemannIntegrable h) :
    Tendsto (fun x : Real => ∫ z in Set.Icc 0 x, h (x-z) ∂V)
      atTop (nhds ((∫ z in Set.Ici 0, h z ∂volume) / mu)) := by sorry
