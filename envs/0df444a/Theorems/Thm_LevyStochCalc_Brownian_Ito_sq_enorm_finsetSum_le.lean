-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_sq_enorm_finsetSum_le
-- name    : LevyStochCalc.Brownian.Ito.sq_enorm_finsetSum_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:44:07.906152+00:00
-- url     : https://prove2.me/theorems/0c93fd35-f584-4c85-93f3-c9a673fb7597
-- title:
--   sq enorm finsetSum le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.sq_enorm_finsetSum_le` is extracted from `LevyStochCalc.Brownian.ItoTruncate`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoTruncate_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Truncating an integrand to a bounded one

Clamping a real integrand to `[-j, j]` leaves a bounded integrand that approximates it in energy:
the clamp is `1`-Lipschitz, fixes `0`, never increases the absolute value, and converges to the
identity pointwise, so dominated convergence gives energy convergence on every window.

## Main statements

* `LevyStochCalc.clampAt` — the clamp.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_clampAt_sub` — the clamped integrand converges to
  the integrand in energy.
-/

namespace LevyStochCalc

open MeasureTheory
open scoped NNReal ENNReal Topology

section Clamp

end Clamp

namespace Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Difference

open LevyStochCalc.Brownian.Multidim

variable {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

theorem _root_.LevyStochCalc.Brownian.Ito.sq_enorm_finsetSum_le {m : ℕ} (x : Fin m → ℝ) :
    (‖∑ k, x k‖₊ : ℝ≥0∞) ^ 2 ≤ (m : ℝ≥0∞) * ∑ k, (‖x k‖₊ : ℝ≥0∞) ^ 2 := by sorry
