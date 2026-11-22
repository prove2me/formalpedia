-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_strictMono_partition_tiles
-- name    : LevyStochCalc.Brownian.Ito.strictMono_partition_tiles
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:54:06.56653+00:00
-- url     : https://prove2.me/theorems/787a3954-fd81-4bbf-a17f-97969a8f6625
-- title:
--   strictMono partition tiles
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.strictMono_partition_tiles` is extracted from `LevyStochCalc.Brownian.SimplePredictableRefineInvariance`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineInvariance_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Refinement of a simple predictable integrand

Refining a `SimplePredictable Ω T` onto a finer partition
(`SimplePredictable.refine`), the pointwise description of the refined
integrand (`SimplePredictable.refine_eval`), and the invariance of the simple
stochastic integral under such a refinement
(`SimplePredictable.simpleIntegral_refine`), obtained by telescoping the driving
increments over each fiber of the refining index map.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.strictMono_partition_tiles
    {M : ℕ} {π' : Fin (M + 1) → ℝ} (h_mono : StrictMono π')
    {s : ℝ} (hs_pos : π' 0 < s) (hs_le_last : s ≤ π' (Fin.last M)) :
    ∃ j : Fin M, π' j.castSucc < s ∧ s ≤ π' j.succ := by sorry
