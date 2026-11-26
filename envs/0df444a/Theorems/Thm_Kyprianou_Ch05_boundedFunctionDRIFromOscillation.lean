-- Prove2me | Theorems.Thm_Kyprianou_Ch05_boundedFunctionDRIFromOscillation
-- name    : Kyprianou.Ch05.boundedFunctionDRIFromOscillation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:58:05.55895+00:00
-- url     : https://prove2.me/theorems/2eb39107-dc44-5a1c-bdce-3f15d878da8c
-- title:
--   Integrable bounded function with uniformly summable grid oscillations is DRI
-- statement:
--   Integrable bounded function with uniformly summable grid oscillations is DRI
-- source:
--   Kyprianou (2006), Lemma 5.5; reduction of the renewal-tail and first-crossing proofs.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.boundedFunctionDRIFromOscillation
    (h : Real → Real) (hi : Integrable h)
    (hn : ∀ t, 0 ≤ h t) (hb : ∀ t, h t ≤ 1)
    (ho : ∀ d : Real, 0 < d →
      Summable (fun k : Int => riCellOscillation h d k) ∧
      (∑' k : Int, riCellOscillation h d k) ≤ 2) :
    DirectlyRiemannIntegrable h := by sorry
