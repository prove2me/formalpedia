-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_tendsto_condExpL2_of_antitone
-- name    : LevyStochCalc.Probability.tendsto_condExpL2_of_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:40:37.691837+00:00
-- url     : https://prove2.me/theorems/1ec631a9-542b-4160-b758-4215be0550bd
-- title:
--   tendsto condExpL2 of antitone
-- statement:
--   The source theorem `LevyStochCalc.Probability.tendsto_condExpL2_of_antitone` is extracted from `LevyStochCalc.Probability.CondExpInf`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_CondExpInf_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# `L²` conditional expectations along a decreasing sequence of σ-algebras

For an antitone sequence of sub-σ-algebras the subspaces `lpMeas (m n)` of `L²` are antitone with
intersection `lpMeas (⨅ n, m n)` (`lpMeas_iInf_of_antitone`, over the `limsup` construction of
`LevyStochCalc.Probability.AEMeasurableInf`), and `condExpL2` is the orthogonal projection onto
them. Projections along an antitone chain of closed subspaces converge to the projection onto the
intersection (`LevyStochCalc.Probability.ProjectionLimit`), so

  `𝔼[f | m n] → 𝔼[f | ⨅ n, m n]` in `L²`.

This is a downward, `L²` counterpart of Lévy's upward theorem
`MeasureTheory.tendsto_eLpNorm_condExp`, the `L¹` convergence along an increasing filtration.
Applied at `m n := ℱ (t + 1/(n+1))` for a right-continuous filtration it gives the
right-`L²`-continuity of `t ↦ 𝔼[ξ | ℱ t]` that the càdlàg regularisation of cited result #13b
needs.

## Main statements

* `lpMeas_iInf_of_antitone` — `⨅ n, lpMeas (m n) = lpMeas (⨅ n, m n)`.
* `tendsto_condExpL2_of_antitone` — the `L²` conditional expectations converge.
-/

open MeasureTheory Filter Topology
open scoped MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*}

variable {m : ℕ → MeasurableSpace Ω} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

theorem _root_.LevyStochCalc.Probability.tendsto_condExpL2_of_antitone (hanti : Antitone m) (hle : ∀ n, m n ≤ m₀)
    (hle_inf : (⨅ n, m n) ≤ m₀) (f : Lp ℝ 2 μ) :
    Tendsto (fun n => ((condExpL2 ℝ ℝ (hle n) f : Lp ℝ 2 μ))) atTop
      (𝓝 ((condExpL2 ℝ ℝ hle_inf f : Lp ℝ 2 μ))) := by sorry
