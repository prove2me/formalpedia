-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_merged_u03c0__zero_p2m_3281419cf2ad
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.merged_u03c0__zero_p2m_3281419cf2ad
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T08:14:19.806182+00:00
-- url     : https://prove2.me/theorems/007d1820-e157-43aa-b155-7c0e0f3307db
-- title:
--   mergedπ zero
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.mergedπ_zero` is extracted from `LevyStochCalc.Brownian.SimplePredictableRefineCommon`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Common refinement of two simple predictables and the difference isometry

The common refinement of two `SimplePredictable Ω T` sharing an endpoint: the
merged set of partition points, the merged partition `SimplePredictable.mergedπ`
with its two refining index maps, the induced refinements
`SimplePredictable.commonRefinement_left`/`_right` and their difference
`SimplePredictable.sub_on_common`. These give the difference isometry for simple
integrals (`SimplePredictable.diff_isometry_simple`) and the Cauchy property of
the simple integrals of an `L²`-Cauchy sequence of simple predictables
(`cauchy_of_L2_dense_simple`).
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.SimplePredictable.merged_u03c0__zero_p2m_3281419cf2ad
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    H₁.mergedπ H₂ 0 = 0 := by sorry
