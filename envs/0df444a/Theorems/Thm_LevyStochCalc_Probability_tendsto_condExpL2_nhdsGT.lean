-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_tendsto_condExpL2_nhdsGT
-- name    : LevyStochCalc.Probability.tendsto_condExpL2_nhdsGT
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:41:22.388818+00:00
-- url     : https://prove2.me/theorems/8b2f62f0-4e86-4811-8bab-a67e6ef55206
-- title:
--   tendsto condExpL2 nhdsGT
-- statement:
--   The source theorem `LevyStochCalc.Probability.tendsto_condExpL2_nhdsGT` is extracted from `LevyStochCalc.Probability.CondExpRightContinuous`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_CondExpRightContinuous_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Right continuity in `L²` of the conditional expectation along a right-continuous filtration

For a filtration `ℱ` indexed by `ℝ` the σ-algebras `ℱ (t + 1/(n+1))` form an antitone sequence
whose infimum is `⨅ r > t, ℱ r`, which is `ℱ t` when `ℱ` is right-continuous. The `L²`
conditional expectations therefore converge to `𝔼[f | ℱ t]` along that sequence
(`LevyStochCalc.Probability.CondExpInf`), and `r ↦ ‖𝔼[f | ℱ r] − 𝔼[f | ℱ t]‖` is monotone on
`[t, ∞)` because the subspaces `lpMeas (ℱ r)` grow, so the convergence upgrades from the sequence
to the filter `𝓝[>] t`.

## Main statements

* `iInf_filtration_add_one_div` — `⨅ n, ℱ (t + 1/(n+1)) = ⨅ r > t, ℱ r`.
* `tendsto_condExpL2_nhdsGT` — `𝔼[f | ℱ r] → 𝔼[f | ℱ t]` in `L²` as `r ↓ t`.
-/

open Filter MeasureTheory Topology
open scoped MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}

section Sequence

variable (ℱ : Filtration ℝ m₀) (t : ℝ)

end Sequence

theorem _root_.LevyStochCalc.Probability.tendsto_condExpL2_nhdsGT (ℱ : Filtration ℝ m₀) [ℱ.IsRightContinuous] (t : ℝ)
    (f : Lp ℝ 2 μ) :
    Tendsto (fun r => ((condExpL2 ℝ ℝ (ℱ.le r) f : Lp ℝ 2 μ))) (𝓝[>] t)
      (𝓝 ((condExpL2 ℝ ℝ (ℱ.le t) f : Lp ℝ 2 μ))) := by sorry
