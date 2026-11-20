-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_tendsto_starProjection_of_antitone
-- name    : LevyStochCalc.Probability.tendsto_starProjection_of_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:39:55.821238+00:00
-- url     : https://prove2.me/theorems/be37549b-14f6-4409-abd6-74aca847de46
-- title:
--   tendsto starProjection of antitone
-- statement:
--   The source theorem `LevyStochCalc.Probability.tendsto_starProjection_of_antitone` is extracted from `LevyStochCalc.Probability.ProjectionLimit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_ProjectionLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonal projections along a decreasing sequence of subspaces

For nested closed subspaces `W ≤ V` the projections compose, `P_W ∘ P_V = P_W`, and Pythagoras
splits the larger projection, `‖P_V x‖² = ‖P_W x‖² + ‖P_V x − P_W x‖²`. Along an antitone sequence
`V 0 ≥ V 1 ≥ ⋯` that makes `n ↦ ‖P_{V n} x‖²` antitone and bounded below, hence convergent, and the
same identity turns its Cauchy property into the Cauchy property of `(P_{V n} x)` itself. The limit
lies in every `V N` and is orthogonal to `⨅ n, V n`, so it *is* the projection onto the
intersection.

This is the Hilbert-space half of the downward `L²` convergence of conditional expectations that
cited result #13b needs; the measure-theoretic half is
`LevyStochCalc/Probability/AEMeasurableInf.lean`, which identifies the intersection of the
`lpMeas` subspaces.

## Main statements

* `starProjection_starProjection_of_le` — the projections compose on nested subspaces.
* `norm_sq_starProjection_of_le` — Pythagoras for nested projections.
* `norm_starProjection_sub_le_of_le` — `‖P_V x − P_U x‖ ≤ ‖P_W x − P_U x‖` for `U ≤ V ≤ W`.
* `tendsto_starProjection_of_antitone` — `P_{V n} x → P_{⨅ V n} x`.
-/

open Filter Topology Submodule

namespace LevyStochCalc.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Antitone

variable {V : ℕ → Submodule ℝ E} [∀ n, (V n).HasOrthogonalProjection]

theorem _root_.LevyStochCalc.Probability.tendsto_starProjection_of_antitone (hV : Antitone V)
    (hclosed : ∀ n, IsClosed ((V n : Set E)))
    [(⨅ n, V n).HasOrthogonalProjection] (x : E) :
    Tendsto (fun n => (V n).starProjection x) atTop (𝓝 ((⨅ n, V n).starProjection x)) := by sorry
