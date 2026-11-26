-- Prove2me | Theorems.Thm_Kyprianou_Ch05_boundedCutoffAntitoneOscillation
-- name    : Kyprianou.Ch05.boundedCutoffAntitoneOscillation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:55:58.08801+00:00
-- url     : https://prove2.me/theorems/1c2cb253-ec69-4aad-995e-13c851137485
-- title:
--   A bounded nonnegative antitone tail cut off below a threshold has bounded total grid oscillation
-- statement:
--   A bounded nonnegative antitone tail cut off below a threshold has bounded total grid oscillation
-- source:
--   Kyprianou (2006), Lemma 5.5; finite-level renewal crossing and tail integrability.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.boundedCutoffAntitoneOscillation
    (g : Real → Real) (hg : Antitone g)
    (hn : ∀ t, 0 ≤ g t) (hb : ∀ t, g t ≤ 1)
    (y d : Real) (hd : 0 < d) :
    Summable (fun k : Int => riCellOscillation
      (fun t : Real => if y < t then g t else 0) d k) ∧
    (∑' k : Int, riCellOscillation
      (fun t : Real => if y < t then g t else 0) d k) ≤ 2 := by sorry
