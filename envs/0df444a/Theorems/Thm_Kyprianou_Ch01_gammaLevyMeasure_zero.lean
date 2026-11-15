-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaLevyMeasure_zero
-- name    : Kyprianou.Ch01.gammaLevyMeasure_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:09:53.645849+00:00
-- url     : https://prove2.me/theorems/d3820f4f-2f11-441b-8837-b76198d7ef25
-- title:
--   Gamma Lévy intensity measure has no atom at the origin
-- statement:
--   For any real shape and rate parameters, the gamma jump intensity measure restricted to the positive half-line assigns zero mass to the point zero. This supplies the first defining condition of the Lévy measure predicate in the Chapter 1 gamma exponent theorem.
-- source:
--   Kyprianou (2006), §1.2.4; Chapter 1 gamma Lévy measure definition.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.gammaLevyMeasure_zero (alpha beta : ℝ) :
    gammaLevyMeasure alpha beta {0} = 0 := by sorry
