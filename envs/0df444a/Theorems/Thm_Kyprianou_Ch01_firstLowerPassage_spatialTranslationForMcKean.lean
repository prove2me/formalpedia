-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstLowerPassage_spatialTranslationForMcKean
-- name    : Kyprianou.Ch01.firstLowerPassage_spatialTranslationForMcKean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:14:13.647147+00:00
-- url     : https://prove2.me/theorems/36a190c5-9175-4384-a6f1-af7afcc801f6
-- title:
--   Spatial translation of strict lower first passage for the McKean put
-- statement:
--   Translation of the initial log-price in a strict lower first-passage time is equivalent to translation of the barrier by the negative starting log-price. This holds pathwise, including infinite passages, and allows application of the already proved Brownian first-lower-passage Laplace transform.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13; Brownian stationary spatial shifts and strict first lower passage.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstLowerPassage_spatialTranslationForMcKean
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (x barrier : ℝ) :
    firstLowerPassage X x barrier =
      firstLowerPassage X 0 (barrier - x) := by sorry
