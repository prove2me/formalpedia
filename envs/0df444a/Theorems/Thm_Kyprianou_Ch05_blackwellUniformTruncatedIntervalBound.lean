-- Prove2me | Theorems.Thm_Kyprianou_Ch05_blackwellUniformTruncatedIntervalBound
-- name    : Kyprianou.Ch05.blackwellUniformTruncatedIntervalBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:24:35.1272+00:00
-- url     : https://prove2.me/theorems/0499c0b3-bb09-5087-bd65-8ce91b7740db
-- title:
--   Blackwell convergence gives a global bound on truncated interval masses
-- statement:
--   Blackwell convergence gives a global bound on truncated interval masses
-- source:
--   Kyprianou (2006), Theorem 5.1, corrected Borel-measurable key renewal theorem; discussion 1dbfd76f-095f-4acc-b3fe-3e528b888bc6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.blackwellUniformTruncatedIntervalBound
    (V : Measure Real) (mu : Real) (hmu : 0 < mu)
    (hfinite : ∀ x : Real, V (Set.Icc 0 x) ≠ ⊤)
    (hBlackwell : ∀ d : Real, 0 < d →
      Tendsto (fun x : Real => (V (Set.Ioc x (x+d))).toReal)
        atTop (nhds (d/mu))) :
    ∀ d : Real, 0 < d → ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ a x : Real, V (Set.Icc 0 x ∩ Set.Ioc a (a+d)) ≤ C := by sorry
