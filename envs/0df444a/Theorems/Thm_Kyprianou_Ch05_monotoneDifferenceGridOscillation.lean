-- Prove2me | Theorems.Thm_Kyprianou_Ch05_monotoneDifferenceGridOscillation
-- name    : Kyprianou.Ch05.monotoneDifferenceGridOscillation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:00:32.643521+00:00
-- url     : https://prove2.me/theorems/6aa0217e-f734-584a-a2f5-ce4baa49c1ca
-- title:
--   Grid oscillation of a monotone difference is bounded by the sum of its endpoint increments
-- statement:
--   Grid oscillation of a monotone difference is bounded by the sum of its endpoint increments
-- source:
--   Kyprianou (2006), Lemma 5.5, renewal-tail estimates.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.monotoneDifferenceGridOscillation
    (p q : Real → Real) (hp : Monotone p) (hq : Monotone q)
    (d : Real) (hd : 0 < d) (k : Int) :
    0 ≤ riCellOscillation (fun t => p t-q t) d k ∧
      riCellOscillation (fun t => p t-q t) d k ≤
        (p (((k : Real)+1)*d)-p ((k : Real)*d)) +
        (q (((k : Real)+1)*d)-q ((k : Real)*d)) := by sorry
