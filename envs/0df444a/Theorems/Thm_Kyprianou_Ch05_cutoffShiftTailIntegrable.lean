-- Prove2me | Theorems.Thm_Kyprianou_Ch05_cutoffShiftTailIntegrable
-- name    : Kyprianou.Ch05.cutoffShiftTailIntegrable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T19:59:01.827503+00:00
-- url     : https://prove2.me/theorems/eb91b001-1dfe-4138-8799-c35b0de4b6c2
-- title:
--   Cutoff shifted nonnegative antitone tail inherits integrability
-- statement:
--   Cutoff shifted nonnegative antitone tail inherits integrability
-- source:
--   Kyprianou (2006), Lemma 5.5.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.cutoffShiftTailIntegrable
    (g : Real → Real) (hg : Antitone g) (hn : ∀ t, 0 ≤ g t)
    (hi : IntegrableOn g (Ioi (0 : Real))) (u y : Real) (hu : 0 < u) (hy : 0 < y) :
    Integrable (fun t : Real => if y < t then g (t+u) else 0) := by sorry
