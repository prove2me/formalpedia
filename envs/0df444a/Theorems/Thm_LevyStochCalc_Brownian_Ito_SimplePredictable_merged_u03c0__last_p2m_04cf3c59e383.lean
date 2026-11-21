-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_merged_u03c0__last_p2m_04cf3c59e383
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.merged_u03c0__last_p2m_04cf3c59e383
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T08:16:11.431769+00:00
-- url     : https://prove2.me/theorems/b6ff2203-155f-43e0-85a5-dbeb668b8df4
-- title:
--   mergedπ last
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.mergedπ_last` is extracted from `LevyStochCalc.Brownian.SimplePredictableRefineCommon`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F001

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

theorem _root_.LevyStochCalc.Brownian.Ito.SimplePredictable.merged_u03c0__last_p2m_04cf3c59e383
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    H₁.mergedπ H₂ (Fin.last (H₁.mergedM H₂)) =
      H₁.partition (Fin.last H₁.N) := by sorry
